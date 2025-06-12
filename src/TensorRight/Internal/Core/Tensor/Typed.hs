{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module TensorRight.Internal.Core.Tensor.Typed
  ( Tensor (Tensor, tensorShape),
    tensorAccess,
    createTensor,
    indicesInRange,
    TensorElem (..),
    reduce,
    NumBinOp (..),
    numBinOp,
    numScalarBinOp,
    BoolBinOp (..),
    boolBinOp,
    boolScalarBinOp,
    CompareOp (..),
    compareOp,
    NumUnaryOp (..),
    numUnaryOp,
    BoolUnaryOp (..),
    boolUnaryOp,
    broadcast,
    iota,
    sliceStartEndStrides,
    pad,
    padLow,
    constant,
    relabel,
    transpose,
    concatTensor,
    concatTensorList,
    dynamicSlice,
    dynamicUpdateSlice,
    dot,
    convBase,
    conv,
    clamp,
    clampScalar,
    reverseTensor,
    select,
    SliceArgs (..),
    DySliceArgs (..),
    PaddingArgs (..),
    ConvConfigArgs (..),
    ConvPaddingArgs (..),
    reshapeDegenerate,
    tensorAssumption,
  )
where

import Control.Monad.Except (MonadError, runExceptT)
import Data.Bifunctor (Bifunctor (first))
import Data.Foldable (traverse_)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable (Hashable (hashWithSalt))
import Data.Tuple (swap)
import GHC.Generics (Generic)
import Grisette
  ( Apply (apply),
    BasicSymPrim,
    EvalSym (evalSym),
    Identifier,
    LinkedRep,
    LogicalOp (symNot, true, (.&&), (.||)),
    Mergeable (rootStrategy),
    MergingStrategy (SimpleStrategy, SortedStrategy),
    MonadUnion,
    PPrint (pformat),
    SimpleMergeable (mrgIte),
    Solvable (con, ssym),
    SymBool,
    SymEq ((./=), (.==)),
    SymInteger,
    SymOrd ((.<), (.<=), (.>), (.>=)),
    forallSym,
    mrgIf,
    mrgReturn,
    mrgTraverse_,
    simpleMerge,
    symAll,
    symAnd,
    symMax,
    type (=~>),
  )
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import TensorRight.Internal.Core.Axis
  ( Axes,
    Axis,
    AxisMapLike
      ( asHashMap,
        fromHashMap,
        fromKVPairs
      ),
    Indices,
    Sizes,
    addAxisMap,
    allAxes,
    castAxisMap,
    foldAxisMap,
    getAxis,
    lookupAxis,
    mapAxisMap,
    mapAxisMapWithAxisKey,
    mulAxisMap,
    removeAxes,
    restrictAxes,
    safeDivAxisMap,
    safeModAxisMap,
    sameAxisMap,
    subAxisMap,
    unionAxisMap,
    zipAxisMap,
    zipFoldAxisMap,
  )
import TensorRight.Internal.Core.Linearization (linearize)
import TensorRight.Internal.Core.Tensor.TensorInt
  ( IsTensorNum,
    TensorDivMod (tensorDiv, tensorRem),
    TensorExp (tensorExp),
    TensorNum,
    nonInf,
    tensorValEq,
    tensorValGe,
    tensorValGt,
    tensorValLe,
    tensorValLt,
    tensorValNe,
    tensorValSymMax,
    tensorValSymMin,
  )
import TensorRight.Internal.Util.Error (Error, ErrorEnv, assert)

data TensorElem elem where
  TensorElemVal :: elem -> TensorElem elem
  TensorElemSum :: (elem ~ TensorNum a) => elem -> TensorElem elem

tensorElemValue :: TensorElem elem -> elem
tensorElemValue (TensorElemVal v) = v
tensorElemValue (TensorElemSum v) = v

instance (Eq elem) => Eq (TensorElem elem) where
  TensorElemVal a == TensorElemVal b = a == b
  TensorElemSum a == TensorElemSum b = a == b
  _ == _ = False

instance (Hashable elem) => Hashable (TensorElem elem) where
  hashWithSalt s (TensorElemVal a) = s `hashWithSalt` (0 :: Int) `hashWithSalt` a
  hashWithSalt s (TensorElemSum a) = s `hashWithSalt` (1 :: Int) `hashWithSalt` a

instance (SymEq elem) => SymEq (TensorElem elem) where
  TensorElemVal a .== TensorElemVal b = a .== b
  TensorElemSum a .== TensorElemSum b = a .== b
  TensorElemVal a .== TensorElemSum b = a .== b
  TensorElemSum a .== TensorElemVal b = a .== b

instance (EvalSym elem) => EvalSym (TensorElem elem) where
  evalSym b m (TensorElemVal a) = TensorElemVal $ evalSym b m a
  evalSym b m (TensorElemSum a) = TensorElemSum $ evalSym b m a

instance (Show elem) => Show (TensorElem elem) where
  show (TensorElemVal i) = show i
  show (TensorElemSum t) = "Sum[" ++ show t ++ "]"

instance (PPrint elem) => PPrint (TensorElem elem) where
  pformat (TensorElemVal i) = pformat i
  pformat (TensorElemSum t) = "Sum[" <> pformat t <> "]"

instance (SimpleMergeable elem) => Mergeable (TensorElem elem) where
  rootStrategy =
    SortedStrategy
      ( \case
          TensorElemVal _ -> 0 :: Int
          TensorElemSum {} -> 1
      )
      ( \case
          0 -> SimpleStrategy $
            \c (TensorElemVal a) (TensorElemVal b) ->
              TensorElemVal $ mrgIte c a b
          _ -> SimpleStrategy $ \c (TensorElemSum a) (TensorElemSum b) ->
            TensorElemSum $ mrgIte c a b
      )

data Tensor elem = Tensor
  { tensorAccessFunc :: Indices -> ErrorEnv (TensorElem elem),
    tensorShape :: Sizes
  }

tensorAssumption ::
  (TensorOperand t elem) =>
  [t] ->
  Indices ->
  ([elem] -> SymBool) ->
  ErrorEnv SymBool
tensorAssumption tensors indices pred = do
  let allAccessed :: SymBool = simpleMerge $ do
        e <- runExceptT (traverse (`tensorAccess` indices) tensors)
        case e of
          Left _ -> return true
          Right elems -> return $ pred $ fmap tensorElemValue elems
  mrgReturn $ forallSym indices allAccessed

tensorAccess ::
  (TensorOperand t elem) =>
  t ->
  Indices ->
  ErrorEnv (TensorElem elem)
tensorAccess to indices = do
  t <- tensor to
  indicesInRange (tensorShape t) indices
  tensorAccessFunc t indices

tensorAllAxes :: Tensor elem -> Axes
tensorAllAxes (Tensor _ dimensions) = allAxes dimensions

instance Show (Tensor elem) where
  show (Tensor _ d) = "Tensor [" ++ show d ++ "]"

instance (SimpleMergeable elem) => Mergeable (Tensor elem) where
  rootStrategy =
    SortedStrategy
      (\(Tensor _ sizes) -> allAxes sizes)
      ( const $ SimpleStrategy $ \c (Tensor a1 d1) (Tensor a2 d2) ->
          Tensor
            (\i -> mrgIf c (a1 i) (a2 i))
            (zipAxisMap (mrgIte c) d1 d2)
      )

class (SimpleMergeable elem) => TensorOperand a elem | a -> elem where
  tensor :: a -> ErrorEnv (Tensor elem)

instance
  (SimpleMergeable elem) =>
  TensorOperand (ErrorEnv (Tensor elem)) elem
  where
  tensor = id

instance (SimpleMergeable elem) => TensorOperand (Tensor elem) elem where
  tensor = mrgReturn

indicesNonNegative :: (MonadError Error m, MonadUnion m) => Sizes -> m ()
indicesNonNegative dims =
  mrgTraverse_
    (\d -> assert "IndicesMap is negative." (d .>= 0))
    (HM.elems $ asHashMap dims)

indicesInRange ::
  (MonadError Error m, MonadUnion m) => Sizes -> Indices -> m ()
indicesInRange dims indices = do
  assert "Axes does not match." $ allAxes dims == allAxes indices
  let assertInRange axis =
        assert
          "Out of range access."
          ( (getAxis axis indices .>= 0)
              .&& (getAxis axis indices .< getAxis axis dims)
          )
  mrgTraverse_ assertInRange $ allAxes dims

class CreateLinearFun elem where
  linearMemory :: Identifier -> SymInteger -> elem

instance CreateLinearFun SymBool where
  linearMemory ident =
    apply (ssym ident :: SymInteger =~> SymBool)

instance
  (LinkedRep ca a, BasicSymPrim a) =>
  CreateLinearFun (TensorNum a)
  where
  linearMemory ident =
    nonInf . apply (ssym ident :: SymInteger =~> a)

createTensor ::
  forall elem.
  ( SimpleMergeable elem,
    CreateLinearFun elem
  ) =>
  Identifier ->
  Sizes ->
  ErrorEnv (Tensor elem)
createTensor ident dims = do
  indicesNonNegative dims
  let memory = linearMemory ident

  mrgReturn $
    Tensor
      ( \indices -> do
          mrgReturn
            . TensorElemVal
            . memory
            . linearize (HS.toList $ allAxes dims) dims
            $ indices
      )
      dims

-- where
--   linearMemory :: FreshT ErrorEnv (SymInteger =~> SymType conElem)
--   linearMemory = simpleFresh ()

reduce ::
  (TensorOperand t (TensorNum a)) =>
  t ->
  Indices ->
  ErrorEnv (Tensor (TensorNum a))
reduce to indicesMap = do
  t <- tensor to
  let reduceAxes = allAxes indicesMap
  assert "IndicesMap must have all axes" $
    reduceAxes `HS.isSubsetOf` allAxes (tensorShape t)
  mrgReturn $
    Tensor
      ( \resultIndices -> do
          assert "Must not have intersection" $
            HS.null $
              reduceAxes `HS.intersection` allAxes resultIndices
          v <- tensorAccess t $ unionAxisMap resultIndices indicesMap
          case v of
            TensorElemVal i -> mrgReturn $ TensorElemSum i
            _ -> mrgReturn v
      )
      (removeAxes reduceAxes $ tensorShape t)

-- | Binary operation for numbers.
data NumBinOp = Add | Mul | Min | Max | Sub | Div | Rem
  deriving (Generic, Eq, Show)
  deriving anyclass (Hashable)

instance PPrint NumBinOp where
  pformat Add = "add"
  pformat Mul = "mul"
  pformat Min = "min"
  pformat Max = "max"
  pformat Sub = "sub"
  pformat Div = "div"
  pformat Rem = "rem"

numBinOp ::
  forall a t1 t2.
  ( TensorOperand t1 (TensorNum a),
    TensorOperand t2 (TensorNum a),
    IsTensorNum a
  ) =>
  NumBinOp ->
  t1 ->
  t2 ->
  ErrorEnv (Tensor (TensorNum a))
numBinOp op xo yo = do
  let func = case op of
        Add -> (+)
        Mul -> (*)
        Min -> tensorValSymMin
        Max -> tensorValSymMax
        Sub -> (-)
        Div -> tensorDiv
        Rem -> tensorRem
  x <- tensor xo
  y <- tensor yo
  assert "Shape mismatch." $ sameAxisMap (tensorShape x) (tensorShape y)
  -- assert "Layout mismatch" $ tensorLinearizedAxes x == tensorLinearizedAxes y
  mrgReturn $
    Tensor
      ( \indices -> do
          xElem <- tensorAccess x indices
          yElem <- tensorAccess y indices
          case (op, xElem, yElem) of
            (_, TensorElemVal xSym, TensorElemVal ySym) -> do
              mrgReturn $ TensorElemVal $ func xSym ySym
            (Mul, TensorElemSum xSym, TensorElemVal ySym) ->
              mrgReturn $ TensorElemSum (xSym * ySym)
            (Mul, TensorElemVal xSym, TensorElemSum ySym) ->
              mrgReturn $ TensorElemSum (xSym * ySym)
            (Mul, TensorElemSum xSym, TensorElemSum ySym) ->
              mrgReturn $ TensorElemSum (xSym * ySym)
            _ -> error "Not implemented"
      )
      (tensorShape x)

numScalarBinOp ::
  ( TensorOperand t (TensorNum a),
    IsTensorNum a
  ) =>
  NumBinOp ->
  t ->
  TensorNum a ->
  ErrorEnv (Tensor (TensorNum a))
numScalarBinOp op xo y = do
  t <- tensor xo
  yTensor <- constant (TensorElemVal y) (tensorShape t)
  numBinOp op xo yTensor

-- | Boolean binary operation.
data BoolBinOp = Or | And
  deriving (Generic, Eq, Show)
  deriving anyclass (Hashable)

instance PPrint BoolBinOp where
  pformat Or = "or"
  pformat And = "and"

boolBinOp ::
  (TensorOperand t1 SymBool, TensorOperand t2 SymBool) =>
  BoolBinOp ->
  t1 ->
  t2 ->
  ErrorEnv (Tensor SymBool)
boolBinOp op xo yo = do
  let func = case op of
        Or -> (.||)
        And -> (.&&)
  x <- tensor xo
  y <- tensor yo
  assert "Shape mismatch." $ sameAxisMap (tensorShape x) (tensorShape y)
  -- assert "Layout mismatch" $ tensorLinearizedAxes x == tensorLinearizedAxes y
  mrgReturn $
    Tensor
      ( \indices -> do
          xElem <- tensorAccess x indices
          yElem <- tensorAccess y indices
          case (op, xElem, yElem) of
            (_, TensorElemVal xSym, TensorElemVal ySym) ->
              mrgReturn $ TensorElemVal $ func xSym ySym
      )
      (tensorShape x)

boolScalarBinOp ::
  (TensorOperand t SymBool) =>
  BoolBinOp ->
  t ->
  SymBool ->
  ErrorEnv (Tensor SymBool)
boolScalarBinOp op xo y = do
  t <- tensor xo
  yTensor <- constant (TensorElemVal y) (tensorShape t)
  boolBinOp op xo yTensor

-- | Integer unary operation.
data NumUnaryOp = Neg | Abs | Exp
  deriving (Generic, Eq, Show)
  deriving anyclass (Hashable)

instance PPrint NumUnaryOp where
  pformat Neg = "neg"
  pformat Abs = "abs"
  pformat Exp = "exp"

numUnaryOp ::
  ( TensorOperand t (TensorNum a),
    IsTensorNum a
  ) =>
  NumUnaryOp ->
  t ->
  ErrorEnv (Tensor (TensorNum a))
numUnaryOp op xo = do
  let func = case op of
        Neg -> negate
        Abs -> abs
        Exp -> tensorExp
  x <- tensor xo
  mrgReturn $
    Tensor
      ( \indices -> do
          xElem <- tensorAccess x indices
          case xElem of
            TensorElemVal xSym -> mrgReturn $ TensorElemVal $ func xSym
            TensorElemSum xSym -> mrgReturn $ TensorElemSum $ func xSym
      )
      (tensorShape x)

-- | Boolean unary operation.
data BoolUnaryOp = Not
  deriving (Generic, Eq, Show)
  deriving anyclass (Hashable)

instance PPrint BoolUnaryOp where
  pformat Not = "not"

boolUnaryOp ::
  (TensorOperand t SymBool) =>
  BoolUnaryOp ->
  t ->
  ErrorEnv (Tensor SymBool)
boolUnaryOp op xo = do
  let func = case op of
        Not -> symNot
  x <- tensor xo
  mrgReturn $
    Tensor
      ( \indices -> do
          xElem <- tensorAccess x indices
          case xElem of
            TensorElemVal xSym -> mrgReturn $ TensorElemVal $ func xSym
      )
      (tensorShape x)

-- | Comparison operation.
data CompareOp = Lt | Le | Eqv | Ne | Ge | Gt
  deriving (Generic, Eq, Show)
  deriving anyclass (Hashable)

instance PPrint CompareOp where
  pformat Lt = "lt"
  pformat Le = "le"
  pformat Eqv = "eqv"
  pformat Ne = "ne"
  pformat Ge = "ge"
  pformat Gt = "gt"

compareOp ::
  ( TensorOperand t1 (TensorNum a),
    TensorOperand t2 (TensorNum a),
    IsTensorNum a
  ) =>
  CompareOp ->
  t1 ->
  t2 ->
  ErrorEnv (Tensor SymBool)
compareOp op xo yo = do
  let func = case op of
        Lt -> tensorValLt
        Le -> tensorValLe
        Eqv -> tensorValEq
        Ne -> tensorValNe
        Ge -> tensorValGe
        Gt -> tensorValGt
  x <- tensor xo
  y <- tensor yo
  assert "Shape mismatch." $ sameAxisMap (tensorShape x) (tensorShape y)
  -- assert "Layout mismatch" $ tensorLinearizedAxes x == tensorLinearizedAxes y
  mrgReturn $
    Tensor
      ( \indices -> do
          xElem <- tensorAccess x indices
          yElem <- tensorAccess y indices
          case (op, xElem, yElem) of
            (_, TensorElemVal xSym, TensorElemVal ySym) -> do
              r <- func xSym ySym
              mrgReturn $ TensorElemVal r
            _ -> error "Not implemented"
      )
      (tensorShape x)

constant ::
  (SimpleMergeable elem) =>
  TensorElem elem ->
  Sizes ->
  ErrorEnv (Tensor elem)
constant v@(TensorElemVal _) dims = do
  indicesNonNegative dims
  mrgReturn $
    Tensor
      (const $ mrgReturn v)
      dims
constant _ _ = mrgThrowError "constant: only support TensorElemVal"

broadcast ::
  (TensorOperand t elem) =>
  t ->
  Sizes ->
  ErrorEnv (Tensor elem)
broadcast to broadcastSizes = do
  t <- tensor to
  let axes = tensorAllAxes t
  let broadcastAxes = allAxes broadcastSizes
  let newAxes = HS.union axes broadcastAxes
  assert "new axes must not exist in the original tensor" $
    HS.null $
      axes `HS.intersection` broadcastAxes
  assert "new axes must have non-negative sizes" $
    symAll (.>= 0) $
      HM.elems $
        asHashMap broadcastSizes
  mrgReturn $
    Tensor
      ( \indices -> do
          assert "indices must have all axes" $ newAxes == allAxes indices
          tensorAccess t $ removeAxes broadcastAxes indices
      )
      (unionAxisMap (tensorShape t) broadcastSizes)

iota :: Sizes -> Axis -> ErrorEnv (Tensor (TensorNum SymInteger))
iota dims axisName = do
  let axes = allAxes dims
  assert "axis must exist in the dimension list" $
    axisName `HS.member` axes
  indicesNonNegative dims
  mrgReturn $
    Tensor
      ( \indices -> do
          assert "indices must have all axes" $ axes == allAxes indices
          mrgReturn $ TensorElemVal $ nonInf $ getAxis axisName indices
      )
      dims

data SliceArgs = SliceArgs
  { start :: Indices,
    end :: Indices,
    strides :: Indices
  }

sliceStartEndStrides ::
  (TensorOperand t elem) =>
  t ->
  SliceArgs ->
  ErrorEnv (Tensor elem)
sliceStartEndStrides to SliceArgs {..} = do
  t <- tensor to
  let axes = tensorAllAxes t
  -- The semantics is different from the original Rosette implementation.
  -- We allow slicing only part of the axes.
  let checkAndFillInAxes name indices valMap = do
        assert (name <> " must be subset of original axes") $
          allAxes indices `HS.isSubsetOf` axes
        let diffDims = axes `HS.difference` allAxes indices
        let emptyIndices =
              restrictAxes diffDims (fromHashMap valMap)
        return $ unionAxisMap indices emptyIndices
  let defaultMap val = HM.fromList . map (,val) . HS.toList
  filledStart <- checkAndFillInAxes "start" start $ (defaultMap 0 axes)
  filledEnd <- checkAndFillInAxes "end" end $ asHashMap (tensorShape t)
  filledStrides <- checkAndFillInAxes "strides" strides $ (defaultMap 1 axes)

  assert "start must be non-negative" $ symAll (.>= 0) $ asHashMap filledStart
  -- The original Rosette implementation may be buggy here.
  assert "end must be greater or equal to start" $
    symAnd $
      zipWith (.>=) (HM.elems $ asHashMap filledEnd) (HM.elems $ asHashMap filledStart)
  assert "strides must be positive" $ symAll (.> 0) $ asHashMap filledStrides
  assert "end must be in the range of the dimension" $
    symAnd $
      zipWith (.<=) (HM.elems $ asHashMap filledEnd) (HM.elems $ asHashMap $ tensorShape t)

  outputShapeSliced <-
    safeDivAxisMap
      (mapAxisMap (\x -> x - 1) $ addAxisMap (subAxisMap filledEnd filledStart) filledStrides)
      filledStrides
  mrgReturn $
    Tensor
      ( \indices -> do
          let slicedIndices =
                addAxisMap filledStart $
                  mulAxisMap filledStrides $
                    restrictAxes (allAxes filledStart) indices
           in tensorAccess t slicedIndices
      )
      (castAxisMap outputShapeSliced)

data PaddingArgs = PaddingArgs
  { lowPad :: Sizes,
    interiorPad :: Sizes,
    highPad :: Sizes
  }
  deriving (Generic, Eq, Show)

pad ::
  (TensorOperand t elem) =>
  t ->
  elem ->
  PaddingArgs ->
  ErrorEnv (Tensor elem)
pad to v PaddingArgs {..} = do
  t <- tensor to
  let axes = tensorAllAxes t
  let checkAndFillInAxes name pad = do
        assert (name <> " must be subset of original axes") $
          allAxes pad `HS.isSubsetOf` axes
        let diffDims = axes `HS.difference` allAxes pad
        let emptyPads =
              fromHashMap $ HS.foldr (`HM.insert` 0) HM.empty diffDims
        return $ unionAxisMap pad emptyPads
  filledPadLow <- checkAndFillInAxes "low" lowPad
  filledPadHigh <- checkAndFillInAxes "high" highPad
  filledPadInterior <- checkAndFillInAxes "interior" interiorPad
  -- assert "low must be non-negative" $ symAll (.>= 0) $ asHashMap padLow
  assert
    "interior must be non-negative"
    $ symAll (.>= 0)
    $ asHashMap filledPadInterior
  -- assert "high must be non-negative" $ symAll (.>= 0) $ asHashMap padHigh
  let numInteriorPadding =
        castAxisMap $
          mapAxisMap (\x -> symMax 0 (x - 1)) $
            tensorShape t ::
          Sizes
  let interiorPaddedShape =
        addAxisMap (mulAxisMap numInteriorPadding filledPadInterior) $
          tensorShape t
  let paddedShape =
        addAxisMap (addAxisMap filledPadLow filledPadHigh) interiorPaddedShape
  assert
    "padded shape must be non-negative"
    $ symAll (.>= 0)
    $ asHashMap paddedShape
  let higherStart = addAxisMap interiorPaddedShape filledPadLow
  let isLowerPaddedArea =
        zipFoldAxisMap (.>) (con False) (.||) filledPadLow . castAxisMap
  let isHigherPaddedArea =
        zipFoldAxisMap (.<=) (con False) (.||) higherStart . castAxisMap
  let isInnerPaddedArea indices = do
        let innerIndices = subAxisMap (castAxisMap indices) filledPadLow
        innerModulo <-
          safeModAxisMap innerIndices (mapAxisMap (+ 1) filledPadInterior)
        mrgReturn $ foldAxisMap (./= 0) (con False) (.||) innerModulo

  let isPaddedArea indices = do
        inner <- isInnerPaddedArea indices
        mrgReturn $
          isLowerPaddedArea indices
            .|| isHigherPaddedArea indices
            .|| inner
  mrgReturn $
    Tensor
      ( \indices -> do
          isPadded <- isPaddedArea indices
          originalIndices <-
            safeDivAxisMap
              (subAxisMap indices $ castAxisMap filledPadLow)
              (mapAxisMap (+ 1) $ castAxisMap filledPadInterior)
          mrgIf
            isPadded
            (mrgReturn $ TensorElemVal v)
            (tensorAccess t originalIndices)
      )
      paddedShape

padLow ::
  (TensorOperand t elem) =>
  t ->
  elem ->
  Sizes ->
  ErrorEnv (Tensor elem)
padLow to v lowPadding = do
  t <- tensor to
  let axes = tensorAllAxes t
  assert "low must be subset of original axes" $
    allAxes lowPadding `HS.isSubsetOf` axes
  let checkAndFillInAxes name pad = do
        assert (name <> " must be subset of original axes") $
          allAxes pad `HS.isSubsetOf` axes
        let diffDims = axes `HS.difference` allAxes pad
        let emptyPads =
              fromHashMap $ HS.foldr (`HM.insert` 0) HM.empty diffDims
        return $ unionAxisMap pad emptyPads
  filledPadLow <- checkAndFillInAxes "low" lowPadding
  let paddedShape =
        addAxisMap filledPadLow $ tensorShape t
  assert
    "padded shape must be non-negative"
    $ symAll (.>= 0)
    $ asHashMap paddedShape
  let isLowerPaddedArea =
        zipFoldAxisMap (.>) (con False) (.||) filledPadLow . castAxisMap

  let isPaddedArea indices = do
        mrgReturn $ isLowerPaddedArea indices
  mrgReturn $
    Tensor
      ( \indices -> do
          isPadded <- isPaddedArea indices
          let originalIndices = subAxisMap indices $ castAxisMap filledPadLow
          mrgIf
            isPadded
            (mrgReturn $ TensorElemVal v)
            (tensorAccess t originalIndices)
      )
      paddedShape

relabel ::
  (TensorOperand t elem) =>
  t ->
  HM.HashMap Axis Axis ->
  ErrorEnv (Tensor elem)
relabel to relabelMap = do
  t <- tensor to
  assert "the relable map should be a subset of all axis" $
    HM.keysSet relabelMap `HS.isSubsetOf` tensorAllAxes t
  let notAugmentedAxes =
        HS.toList $ tensorAllAxes t `HS.difference` HM.keysSet relabelMap
  let augmentedRelabelMap =
        HM.union relabelMap $
          HM.fromList $
            (\x -> (x, x)) <$> notAugmentedAxes
  assert "no two axes mapped to the same axis" $
    HS.size (HS.fromList $ HM.elems augmentedRelabelMap)
      == HM.size augmentedRelabelMap
  let reverseMap = HM.fromList $ map swap $ HM.toList augmentedRelabelMap
  mrgReturn $
    Tensor
      ( \indices -> do
          let newIndices =
                HM.fromList $
                  fmap (first (reverseMap HM.!)) $
                    HM.toList $
                      asHashMap indices
          tensorAccess t $ fromHashMap newIndices
      )
      ( fromHashMap $
          HM.fromList $
            fmap (first (augmentedRelabelMap HM.!)) $
              HM.toList $
                asHashMap $
                  tensorShape t
      )

transpose ::
  (TensorOperand t elem) =>
  t ->
  HM.HashMap Axis Axis ->
  ErrorEnv (Tensor elem)
transpose to permutation = do
  t <- tensor to
  assert "transpose wants a permutation" $
    HM.keysSet permutation == HS.fromList (HM.elems permutation)
  relabel t permutation

concatTensor ::
  ( TensorOperand t1 elem,
    TensorOperand t2 elem
  ) =>
  t1 ->
  t2 ->
  Axis ->
  ErrorEnv (Tensor elem)
concatTensor to1 to2 axis = do
  t1 <- tensor to1
  t2 <- tensor to2
  let axes1 = tensorAllAxes t1
  let axes2 = tensorAllAxes t2
  assert "axes must be the same" $ axes1 == axes2
  assert "axis must exist in the tensors" $
    axis `HS.member` axes1

  let t1ConcatAxisSize = getAxis axis $ tensorShape t1
  let t2ConcatAxisSize = getAxis axis $ tensorShape t2

  let t1OtherAxisSize = removeAxes (HS.singleton axis) $ tensorShape t1
  let t2OtherAxisSize = removeAxes (HS.singleton axis) $ tensorShape t2
  assert "other axes must have the same size" $
    t1OtherAxisSize .== t2OtherAxisSize
  let newShape =
        unionAxisMap
          (fromKVPairs [(axis, t1ConcatAxisSize + t2ConcatAxisSize)])
          t1OtherAxisSize
  mrgReturn $
    Tensor
      ( \indices -> do
          let concatIndex = getAxis axis indices
          let otherIndices = removeAxes (HS.singleton axis) indices
          mrgIf
            (concatIndex .< t1ConcatAxisSize)
            ( tensorAccess t1 $
                unionAxisMap
                  (fromKVPairs [(axis, concatIndex)])
                  otherIndices
            )
            ( tensorAccess t2 $
                unionAxisMap
                  (fromKVPairs [(axis, concatIndex - t1ConcatAxisSize)])
                  otherIndices
            )
      )
      newShape

concatTensorList ::
  (TensorOperand t elem) =>
  [t] ->
  Axis ->
  ErrorEnv (Tensor elem)
concatTensorList [] _ = mrgThrowError "concatTensorList: empty list"
concatTensorList [to] _ = tensor to
concatTensorList (to : ts) axis = do
  t <- tensor to
  ts' <- concatTensorList ts axis
  concatTensor t ts' axis

data DySliceArgs = DySliceArgs
  { start :: Indices,
    sizes :: Sizes
  }

dynamicSlice ::
  (TensorOperand t elem) => t -> DySliceArgs -> ErrorEnv (Tensor elem)
dynamicSlice to DySliceArgs {..} = do
  t <- tensor to
  assert "start must have the same axes as sizes" $
    allAxes start == allAxes sizes
  assert "sizes must be a subset of the original axes" $
    allAxes sizes `HS.isSubsetOf` tensorAllAxes t
  let otherOriginalShape = removeAxes (allAxes sizes) $ tensorShape t
  assert "sizes must be strictly positive" $ symAll (.> 0) $ asHashMap sizes
  assert "start must be non-negative" $ symAll (.>= 0) $ asHashMap start
  assert "start + sizes must be in the range of the dimension" $
    symAnd $
      HM.mapWithKey
        (\k e -> e .<= getAxis k (tensorShape t))
        (asHashMap $ addAxisMap start $ castAxisMap sizes)
  let newShape = unionAxisMap sizes otherOriginalShape
  mrgReturn $
    Tensor
      ( \indices -> do
          let slicedIndices =
                addAxisMap start $ restrictAxes (allAxes sizes) indices
          let otherIndices = removeAxes (allAxes sizes) indices
          tensorAccess t $ unionAxisMap slicedIndices otherIndices
      )
      newShape

dynamicUpdateSlice ::
  ( TensorOperand t1 elem,
    TensorOperand t2 elem
  ) =>
  t1 ->
  t2 ->
  Indices ->
  ErrorEnv (Tensor elem)
dynamicUpdateSlice to update start = do
  t <- tensor to
  u <- tensor update
  assert "start must have the same axes as update" $
    allAxes start == allAxes (tensorShape u)
  assert "update must have the same axes as original" $
    tensorAllAxes t == tensorAllAxes u
  assert "start must be non-negative" $ symAll (.>= 0) $ asHashMap start
  assert "update sizes must be strictly positive" $
    symAll (.> 0) $
      asHashMap $
        tensorShape u
  assert "start + update must be in the range of the dimension" $
    symAnd $
      HM.mapWithKey
        (\k e -> e .<= getAxis k (tensorShape t))
        (asHashMap $ addAxisMap start $ castAxisMap (tensorShape u))
  mrgReturn $
    Tensor
      ( \indices -> do
          let geqStart = zipFoldAxisMap (.>=) (con True) (.&&) indices start
          let leqUpdateEnd =
                zipFoldAxisMap
                  (.<)
                  (con True)
                  (.&&)
                  indices
                  (addAxisMap start $ castAxisMap $ tensorShape u)
          mrgIf
            (geqStart .&& leqUpdateEnd)
            (tensorAccess u $ subAxisMap indices start)
            (tensorAccess t indices)
      )
      (tensorShape t)

dot ::
  ( TensorOperand t1 (TensorNum a),
    TensorOperand t2 (TensorNum a),
    IsTensorNum a
  ) =>
  t1 ->
  t2 ->
  Indices ->
  Axes ->
  ErrorEnv (Tensor (TensorNum a))
dot to1 to2 contractionSIMap batchAxes = do
  t1 <- tensor to1
  t2 <- tensor to2
  let contractionAxes = allAxes contractionSIMap
  let t1Axes = tensorAllAxes t1
  let t2Axes = tensorAllAxes t2
  assert "Contraction axes and batch axes must be disjoint." $
    (contractionAxes `HS.intersection` batchAxes) == HS.empty
  let dotAxes = contractionAxes `HS.union` batchAxes
  assert
    ( "Contraction + batch axes should be exactly the intersection of t1 and "
        <> "t2 axes."
    )
    $ dotAxes == (t1Axes `HS.intersection` t2Axes)
  let t1BroadcastSizes = removeAxes dotAxes $ tensorShape t2
  let t2BroadcastSizes = removeAxes dotAxes $ tensorShape t1
  reduce
    ( numBinOp
        Mul
        (broadcast t1 t1BroadcastSizes)
        (broadcast t2 t2BroadcastSizes)
    )
    contractionSIMap

data ConvConfigArgs = ConvConfigArgs
  { convBatchAxes :: Axes,
    convFeatureAxes :: Axes,
    convOutputFeatureAxes :: Axes,
    convStrides :: Indices,
    convContractingSIMap :: Indices
  }

convBase ::
  ( TensorOperand t1 (TensorNum a),
    TensorOperand t2 (TensorNum a),
    IsTensorNum a
  ) =>
  t1 ->
  t2 ->
  ConvConfigArgs ->
  ErrorEnv (Tensor (TensorNum a))
convBase inputo weightso ConvConfigArgs {..} = do
  input <- tensor inputo
  weights <- tensor weightso
  let inputShape = tensorShape input
  let weightShape = tensorShape weights
  let inputAxes = tensorAllAxes input
  let weightAxes = tensorAllAxes weights
  assert "batch axes should be input axes - weight axes" $
    convBatchAxes == inputAxes `HS.difference` weightAxes
  assert "output feature axes should be weight axes - input axes" $
    convOutputFeatureAxes == weightAxes `HS.difference` inputAxes
  assert
    "input feature should be in the intersection of input and weight axes"
    $ convFeatureAxes `HS.isSubsetOf` (inputAxes `HS.intersection` weightAxes)
  let spatialAxes =
        inputAxes `HS.difference` (convBatchAxes `HS.union` convFeatureAxes)
  assert "strides should have the same axes as spatial axes" $
    allAxes convStrides == spatialAxes
  let inputSpatialShape = restrictAxes spatialAxes inputShape
  let weightSpatialShape = restrictAxes spatialAxes weightShape
  resultSpatialShape <-
    safeDivAxisMap
      ( addAxisMap
          (subAxisMap inputSpatialShape weightSpatialShape)
          (castAxisMap convStrides)
      )
      $ castAxisMap convStrides
  let resultShape =
        unionAxisMap
          (restrictAxes convBatchAxes inputShape)
          $ unionAxisMap
            (restrictAxes convOutputFeatureAxes weightShape)
            resultSpatialShape
  let sub asp =
        dot
          ( sliceStartEndStrides input $
              SliceArgs
                { start = mulAxisMap asp convStrides,
                  end =
                    addAxisMap (mulAxisMap asp convStrides) $
                      castAxisMap weightSpatialShape,
                  strides = mapAxisMap (const 1) asp
                }
          )
          weights
          convContractingSIMap
          HS.empty
  mrgReturn $
    Tensor
      ( \m -> do
          let asp = restrictAxes spatialAxes m
          let asub =
                restrictAxes (HS.union convBatchAxes convOutputFeatureAxes) m
          tensorAccess (sub asp) asub
      )
      resultShape

data ConvPaddingArgs = ConvPaddingArgs
  { convLowPadding :: Sizes,
    convLDilation :: Sizes,
    convHighPadding :: Sizes,
    convRDilation :: Sizes
  }

conv ::
  ( TensorOperand t1 (TensorNum a),
    TensorOperand t2 (TensorNum a),
    IsTensorNum a
  ) =>
  t1 ->
  t2 ->
  ConvConfigArgs ->
  ConvPaddingArgs ->
  ErrorEnv (Tensor (TensorNum a))
conv input weights convBaseConfig ConvPaddingArgs {..} = do
  let paddedInput =
        pad input 0 $
          PaddingArgs
            { lowPad = convLowPadding,
              interiorPad = mapAxisMap (\x -> x - 1) convLDilation,
              highPad = convHighPadding
            }
  let paddedWeights =
        pad weights 0 $
          PaddingArgs
            { lowPad = fromKVPairs [],
              interiorPad = mapAxisMap (\x -> x - 1) convRDilation,
              highPad = fromKVPairs []
            }
  convBase paddedInput paddedWeights convBaseConfig

clamp ::
  ( TensorOperand t (TensorNum a),
    TensorOperand tmin (TensorNum a),
    TensorOperand tmax (TensorNum a),
    IsTensorNum a
  ) =>
  tmin ->
  t ->
  tmax ->
  ErrorEnv (Tensor (TensorNum a))
clamp mino to maxo = do
  min' <- tensor mino
  t <- tensor to
  max' <- tensor maxo
  assert "clamp: min and max must have the same shape as the tensor" $
    tensorShape min' .== tensorShape t
  assert "clamp: min and max must have the same shape as the tensor" $
    tensorShape max' .== tensorShape t
  mrgReturn $
    Tensor
      ( \indices -> do
          minElem <- tensorAccess min' indices
          tElem <- tensorAccess t indices
          maxElem <- tensorAccess max' indices
          case (minElem, tElem, maxElem) of
            (TensorElemVal minSym, TensorElemVal tSym, TensorElemVal maxSym) ->
              mrgReturn $ TensorElemVal $ tensorValSymMin maxSym $ tensorValSymMax tSym minSym
            _ -> error "Not implemented"
      )
      (tensorShape t)

clampScalar ::
  ( TensorOperand t (TensorNum a),
    IsTensorNum a
  ) =>
  TensorNum a ->
  t ->
  TensorNum a ->
  ErrorEnv (Tensor (TensorNum a))
clampScalar min to max = do
  t <- tensor to
  min' <- constant (TensorElemVal min) (tensorShape t)
  max' <- constant (TensorElemVal max) (tensorShape t)
  clamp min' to max'

reverseTensor :: (TensorOperand t elem) => t -> Axes -> ErrorEnv (Tensor elem)
reverseTensor to axes = do
  t <- tensor to
  let allAxes = tensorAllAxes t
  assert "reverseTensor: axes must be a subset of the tensor axes" $
    axes `HS.isSubsetOf` allAxes
  let shape = tensorShape t
  mrgReturn $
    Tensor
      ( \indices -> do
          let reversedIndices =
                mapAxisMapWithAxisKey
                  ( \axis i ->
                      if axis `HS.member` axes
                        then getAxis axis shape - i - 1
                        else i
                  )
                  indices
          tensorAccess t reversedIndices
      )
      shape

select ::
  ( TensorOperand tpred SymBool,
    TensorOperand ttrue elem,
    TensorOperand tfalse elem
  ) =>
  tpred ->
  ttrue ->
  tfalse ->
  ErrorEnv (Tensor elem)
select predo ttrueo tfalseo = do
  pred <- tensor predo
  ttrue <- tensor ttrueo
  tfalse <- tensor tfalseo
  let shape = tensorShape ttrue
  assert "select: pred must have the same shape as the tensors" $
    tensorShape pred .== shape
  assert "select: pred must have the same shape as the tensors" $
    tensorShape tfalse .== shape
  mrgReturn $
    Tensor
      ( \indices -> do
          predElem <- tensorAccess pred indices
          case predElem of
            TensorElemVal pred ->
              mrgIf
                pred
                (tensorAccess ttrue indices)
                (tensorAccess tfalse indices)
      )
      shape

reshapeDegenerate ::
  (TensorOperand t elem) =>
  t ->
  Axes ->
  Axes ->
  ErrorEnv (Tensor elem)
reshapeDegenerate to introAxes removedAxes = do
  t <- tensor to
  let shape = tensorShape t
  let axes = tensorAllAxes t
  assert "reshapeDegenerate: intro axes must not exist in the tensor" $
    HS.null $
      introAxes `HS.intersection` axes
  traverse_
    ( \axis -> do
        case lookupAxis axis shape of
          Nothing -> mrgThrowError "reshapeDegenerate: axis not found"
          Just n -> assert "reshapeDegenerate: axis must have size 1" $ n .== 1
    )
    $ HS.toList removedAxes
  let newShape =
        unionAxisMap (fromKVPairs ((,1) <$> HS.toList introAxes)) $
          removeAxes removedAxes shape
  mrgReturn $
    Tensor
      ( \indices -> do
          let originalIndices = removeAxes introAxes indices
          tensorAccess t $
            unionAxisMap
              (fromKVPairs ((,0) <$> HS.toList removedAxes))
              originalIndices
      )
      newShape
