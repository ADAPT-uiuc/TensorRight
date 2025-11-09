{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TensorRight.Internal.Core.Tensor
  ( Tensor (..),
    Typed.NumBinOp (..),
    Typed.BoolBinOp (..),
    DType (..),
    ToDType (..),
    Elem (..),
    elemDType,
    ToElem (..),
    createTensor,
    tensorAccess,
    reduce,
    numBinOp,
    numScalarBinOp,
    boolBinOp,
    boolScalarBinOp,
    broadcast,
    tensorDType,
    tensorShape,
    compareOp,
    numUnaryOp,
    boolUnaryOp,
    constantTensor,
    iota,
    slice,
    pad,
    padLow,
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
    reshapeDegenerate,
    numTensorAssumption,
  )
where

import qualified Data.HashMap.Lazy as HM
import Data.Hashable (Hashable)
import GHC.Generics (Generic)
import Grisette
  ( Default (Default),
    EvalSym,
    Identifier,
    Mergeable,
    PPrint,
    SimpleMergeable,
    SymBool,
    mrgFmap,
    mrgReturn,
  )
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import TensorRight.Internal.Core.Axis (Axes, Axis, Indices, Sizes)
import TensorRight.Internal.Core.Tensor.TensorInt (IsTensorNum, TensorInt, TensorNum, TensorReal)
import TensorRight.Internal.Core.Tensor.Typed
  ( ConvConfigArgs,
    ConvPaddingArgs,
    PaddingArgs,
  )
import qualified TensorRight.Internal.Core.Tensor.Typed as Typed
import TensorRight.Internal.Util.Error (ErrorEnv)

-- | The data type of a tensor.
--
-- We currently support three data types: integers, reals, and booleans.
--
-- The integer or real type is using a special representation ('TensorNum') that
-- allows representing +inf and -inf.
data DType = IntType | RealType | BoolType
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (PPrint) via (Default DType)

class ToDType a where
  toDType :: a -> DType

instance ToDType TensorInt where
  toDType _ = IntType

instance ToDType TensorReal where
  toDType _ = RealType

instance ToDType SymBool where
  toDType _ = BoolType

data Tensor where
  RealTensor :: Typed.Tensor TensorReal -> Tensor
  IntTensor :: Typed.Tensor TensorInt -> Tensor
  BoolTensor :: Typed.Tensor SymBool -> Tensor
  deriving (Show, Generic)
  deriving (Mergeable) via (Default Tensor)

class (Mergeable a) => ToUntypedTensor a where
  toUntypedTensor :: a -> Tensor

instance ToUntypedTensor (Typed.Tensor TensorInt) where
  toUntypedTensor = IntTensor

instance ToUntypedTensor (Typed.Tensor TensorReal) where
  toUntypedTensor = RealTensor

instance ToUntypedTensor (Typed.Tensor SymBool) where
  toUntypedTensor = BoolTensor

tensorDType :: Tensor -> DType
tensorDType (RealTensor _) = RealType
tensorDType (IntTensor _) = IntType
tensorDType (BoolTensor _) = BoolType

tensorShape :: Tensor -> Sizes
tensorShape (RealTensor t) = Typed.tensorShape t
tensorShape (IntTensor t) = Typed.tensorShape t
tensorShape (BoolTensor t) = Typed.tensorShape t

class TensorOperand a where
  tensor :: a -> ErrorEnv Tensor

instance TensorOperand Tensor where
  tensor = mrgReturn

instance TensorOperand (ErrorEnv Tensor) where
  tensor = id

data Elem where
  RealElem :: Typed.TensorElem TensorReal -> Elem
  IntElem :: Typed.TensorElem TensorInt -> Elem
  BoolElem :: Typed.TensorElem SymBool -> Elem
  deriving (Generic, Eq, Show)
  deriving (Hashable)
  deriving (EvalSym, PPrint, Mergeable) via (Default Elem)

elemDType :: Elem -> DType
elemDType (RealElem _) = RealType
elemDType (IntElem _) = IntType
elemDType (BoolElem _) = BoolType

class ToElem a where
  toElem :: a -> Elem

instance ToElem TensorInt where
  toElem = IntElem . Typed.TensorElemVal

instance ToElem TensorReal where
  toElem = RealElem . Typed.TensorElemVal

instance ToElem SymBool where
  toElem = BoolElem . Typed.TensorElemVal

instance ToElem Elem where
  toElem = id

tensorAccess :: (TensorOperand t) => t -> Indices -> ErrorEnv Elem
tensorAccess to i = do
  t <- tensor to
  case t of
    RealTensor t' -> do
      r <- Typed.tensorAccess t' i
      mrgReturn $ RealElem r
    IntTensor t' -> do
      r <- Typed.tensorAccess t' i
      mrgReturn $ IntElem r
    BoolTensor t' -> do
      r <- Typed.tensorAccess t' i
      mrgReturn $ BoolElem r

createTensor ::
  Identifier ->
  Sizes ->
  DType ->
  ErrorEnv Tensor
createTensor ident dims RealType =
  mrgFmap RealTensor $ Typed.createTensor ident dims
createTensor ident dims IntType =
  mrgFmap IntTensor $ Typed.createTensor ident dims
createTensor ident dims BoolType =
  mrgFmap BoolTensor $ Typed.createTensor ident dims

applyValUnary ::
  (Typed.Tensor TensorReal -> ErrorEnv (Typed.Tensor TensorReal)) ->
  (Typed.Tensor TensorInt -> ErrorEnv (Typed.Tensor TensorInt)) ->
  Tensor ->
  ErrorEnv Tensor
applyValUnary f _ (RealTensor t) = mrgFmap RealTensor $ f t
applyValUnary _ f (IntTensor t) = mrgFmap IntTensor $ f t
applyValUnary _ _ _ = mrgThrowError "applyValUnary: only support ValTensors"

applyValUnaryWithElem ::
  ( Typed.Tensor TensorReal ->
    TensorReal ->
    ErrorEnv (Typed.Tensor TensorReal)
  ) ->
  ( Typed.Tensor TensorInt ->
    TensorInt ->
    ErrorEnv (Typed.Tensor TensorInt)
  ) ->
  Tensor ->
  Elem ->
  ErrorEnv Tensor
applyValUnaryWithElem f _ (RealTensor t) (RealElem (Typed.TensorElemVal e)) =
  mrgFmap RealTensor $ f t e
applyValUnaryWithElem _ f (IntTensor t) (IntElem (Typed.TensorElemVal e)) =
  mrgFmap IntTensor $ f t e
applyValUnaryWithElem _ _ _ _ =
  mrgThrowError
    "applyIntUnary: only support IntTensors and using a value elements"

applyBoolUnary ::
  (Typed.Tensor SymBool -> ErrorEnv (Typed.Tensor SymBool)) ->
  Tensor ->
  ErrorEnv Tensor
applyBoolUnary f (BoolTensor t) = mrgFmap BoolTensor $ f t
applyBoolUnary _ _ = mrgThrowError "applyBoolUnary: only support BoolTensors"

applyBoolUnaryWithElem ::
  ( Typed.Tensor SymBool ->
    SymBool ->
    ErrorEnv (Typed.Tensor SymBool)
  ) ->
  Tensor ->
  Elem ->
  ErrorEnv Tensor
applyBoolUnaryWithElem f (BoolTensor t) (BoolElem (Typed.TensorElemVal e)) =
  mrgFmap BoolTensor $ f t e
applyBoolUnaryWithElem _ _ _ =
  mrgThrowError
    "applyBoolUnary: only support BoolTensors and using a value elements"

genericApplyUnary ::
  ( forall a.
    (SimpleMergeable a) =>
    Typed.Tensor a ->
    ErrorEnv (Typed.Tensor a)
  ) ->
  Tensor ->
  ErrorEnv Tensor
genericApplyUnary f (RealTensor t) = mrgFmap RealTensor $ f t
genericApplyUnary f (IntTensor t) = mrgFmap IntTensor $ f t
genericApplyUnary f (BoolTensor t) = mrgFmap BoolTensor $ f t

genericApplyUnaryWithElem ::
  ( forall a.
    (SimpleMergeable a) =>
    Typed.Tensor a ->
    a ->
    ErrorEnv (Typed.Tensor a)
  ) ->
  Tensor ->
  Elem ->
  ErrorEnv Tensor
genericApplyUnaryWithElem f (RealTensor t) (RealElem (Typed.TensorElemVal e)) =
  mrgFmap RealTensor $ f t e
genericApplyUnaryWithElem f (IntTensor t) (IntElem (Typed.TensorElemVal e)) =
  mrgFmap IntTensor $ f t e
genericApplyUnaryWithElem f (BoolTensor t) (BoolElem (Typed.TensorElemVal e)) =
  mrgFmap BoolTensor $ f t e
genericApplyUnaryWithElem _ _ _ =
  mrgThrowError
    "genericApplyUnaryWithElem: type mismatch or using a non-val element"

applyValBinary ::
  ( Typed.Tensor TensorReal ->
    Typed.Tensor TensorReal ->
    ErrorEnv (Typed.Tensor TensorReal)
  ) ->
  ( Typed.Tensor TensorInt ->
    Typed.Tensor TensorInt ->
    ErrorEnv (Typed.Tensor TensorInt)
  ) ->
  Tensor ->
  Tensor ->
  ErrorEnv Tensor
applyValBinary f _ (RealTensor t1) (RealTensor t2) =
  mrgFmap toUntypedTensor $ f t1 t2
applyValBinary _ f (IntTensor t1) (IntTensor t2) =
  mrgFmap toUntypedTensor $ f t1 t2
applyValBinary _ _ _ _ = mrgThrowError "applyValBinary: type mismatch"

applyValCompare ::
  ( Typed.Tensor TensorReal ->
    Typed.Tensor TensorReal ->
    ErrorEnv (Typed.Tensor SymBool)
  ) ->
  ( Typed.Tensor TensorInt ->
    Typed.Tensor TensorInt ->
    ErrorEnv (Typed.Tensor SymBool)
  ) ->
  Tensor ->
  Tensor ->
  ErrorEnv Tensor
applyValCompare f _ (RealTensor t1) (RealTensor t2) =
  mrgFmap toUntypedTensor $ f t1 t2
applyValCompare _ f (IntTensor t1) (IntTensor t2) =
  mrgFmap toUntypedTensor $ f t1 t2
applyValCompare _ _ _ _ = mrgThrowError "applyIntBinary: type mismatch"

applyBoolBinary ::
  (ToUntypedTensor t) =>
  ( Typed.Tensor SymBool ->
    Typed.Tensor SymBool ->
    ErrorEnv t
  ) ->
  Tensor ->
  Tensor ->
  ErrorEnv Tensor
applyBoolBinary f (BoolTensor t1) (BoolTensor t2) =
  mrgFmap toUntypedTensor $ f t1 t2
applyBoolBinary _ _ _ = mrgThrowError "applyBoolBinary: type mismatch"

genericApplyBinary ::
  ( forall a.
    (SimpleMergeable a) =>
    Typed.Tensor a ->
    Typed.Tensor a ->
    ErrorEnv (Typed.Tensor a)
  ) ->
  Tensor ->
  Tensor ->
  ErrorEnv Tensor
genericApplyBinary f (RealTensor t1) (RealTensor t2) =
  mrgFmap RealTensor $ f t1 t2
genericApplyBinary f (IntTensor t1) (IntTensor t2) =
  mrgFmap IntTensor $ f t1 t2
genericApplyBinary f (BoolTensor t1) (BoolTensor t2) =
  mrgFmap BoolTensor $ f t1 t2
genericApplyBinary _ _ _ = mrgThrowError "genericApplyBinary: type mismatch"

numBinOp ::
  (TensorOperand t1, TensorOperand t2) =>
  Typed.NumBinOp ->
  t1 ->
  t2 ->
  ErrorEnv Tensor
numBinOp op t1 t2 = do
  t1' <- tensor t1
  t2' <- tensor t2
  applyValBinary (Typed.numBinOp op) (Typed.numBinOp op) t1' t2'

numScalarBinOp ::
  (TensorOperand t) =>
  Typed.NumBinOp ->
  t ->
  Elem ->
  ErrorEnv Tensor
numScalarBinOp op to scalar = do
  t <- tensor to
  applyValUnaryWithElem
    (Typed.numScalarBinOp op)
    (Typed.numScalarBinOp op)
    t
    scalar

boolScalarBinOp ::
  (TensorOperand t) =>
  Typed.BoolBinOp ->
  t ->
  Elem ->
  ErrorEnv Tensor
boolScalarBinOp op to scalar = do
  t <- tensor to
  applyBoolUnaryWithElem (Typed.boolScalarBinOp op) t scalar

boolBinOp ::
  (TensorOperand t1, TensorOperand t2) =>
  Typed.BoolBinOp ->
  t1 ->
  t2 ->
  ErrorEnv Tensor
boolBinOp op t1 t2 = do
  t1' <- tensor t1
  t2' <- tensor t2
  applyBoolBinary (Typed.boolBinOp op) t1' t2'

numUnaryOp ::
  (TensorOperand t) =>
  Typed.NumUnaryOp ->
  t ->
  ErrorEnv Tensor
numUnaryOp op to = do
  t <- tensor to
  applyValUnary (Typed.numUnaryOp op) (Typed.numUnaryOp op) t

boolUnaryOp ::
  (TensorOperand t) =>
  Typed.BoolUnaryOp ->
  t ->
  ErrorEnv Tensor
boolUnaryOp op to = do
  t <- tensor to
  applyBoolUnary (Typed.boolUnaryOp op) t

compareOp ::
  (TensorOperand t1, TensorOperand t2) =>
  Typed.CompareOp ->
  t1 ->
  t2 ->
  ErrorEnv Tensor
compareOp op t1 t2 = do
  t1' <- tensor t1
  t2' <- tensor t2
  applyValCompare (Typed.compareOp op) (Typed.compareOp op) t1' t2'

reduce :: (TensorOperand t) => t -> Indices -> ErrorEnv Tensor
reduce to i = do
  t <- tensor to
  applyValUnary (`Typed.reduce` i) (`Typed.reduce` i) t

broadcast :: (TensorOperand t) => t -> Sizes -> ErrorEnv Tensor
broadcast to broadcastSizes =
  genericApplyUnary (`Typed.broadcast` broadcastSizes)
    =<< tensor to

constantTensor ::
  Elem ->
  Sizes ->
  ErrorEnv Tensor
constantTensor (RealElem a) dims = mrgFmap toUntypedTensor $ Typed.constant a dims
constantTensor (IntElem a) dims = mrgFmap toUntypedTensor $ Typed.constant a dims
constantTensor (BoolElem a) dims = mrgFmap toUntypedTensor $ Typed.constant a dims

iota :: Sizes -> Axis -> ErrorEnv Tensor
iota dims axisName = Typed.iota dims axisName >>= (mrgReturn . IntTensor)

slice ::
  (TensorOperand t) => t -> Typed.SliceArgs -> ErrorEnv Tensor
slice to args =
  genericApplyUnary (`Typed.sliceStartEndStrides` args)
    =<< tensor to

pad ::
  (TensorOperand t) =>
  t ->
  Elem ->
  PaddingArgs ->
  ErrorEnv Tensor
pad to elem config = do
  t <- tensor to
  genericApplyUnaryWithElem (\t e -> Typed.pad t e config) t elem

padLow ::
  (TensorOperand t) =>
  t ->
  Elem ->
  Sizes ->
  ErrorEnv Tensor
padLow to elem lowPadConfig = do
  t <- tensor to
  genericApplyUnaryWithElem (\t e -> Typed.padLow t e lowPadConfig) t elem

relabel :: (TensorOperand t) => t -> HM.HashMap Axis Axis -> ErrorEnv Tensor
relabel to permutation =
  genericApplyUnary (`Typed.relabel` permutation) =<< tensor to

transpose :: (TensorOperand t) => t -> HM.HashMap Axis Axis -> ErrorEnv Tensor
transpose to permutation =
  genericApplyUnary (`Typed.transpose` permutation) =<< tensor to

concatTensor ::
  (TensorOperand t1, TensorOperand t2) =>
  t1 ->
  t2 ->
  Axis ->
  ErrorEnv Tensor
concatTensor t1 t2 axis = do
  t1' <- tensor t1
  t2' <- tensor t2
  genericApplyBinary (\t1 t2 -> Typed.concatTensor t1 t2 axis) t1' t2'

concatTensorList ::
  (TensorOperand t) =>
  [t] ->
  Axis ->
  ErrorEnv Tensor
concatTensorList [] _ = mrgThrowError "concatTensorList: empty list"
concatTensorList [to] _ = tensor to
concatTensorList (to : ts) axis = do
  t <- tensor to
  ts' <- concatTensorList ts axis
  concatTensor t ts' axis

dynamicSlice ::
  (TensorOperand t) =>
  t ->
  Typed.DySliceArgs ->
  ErrorEnv Tensor
dynamicSlice to args =
  genericApplyUnary (`Typed.dynamicSlice` args) =<< tensor to

dynamicUpdateSlice ::
  (TensorOperand t1, TensorOperand t2) =>
  t1 ->
  t2 ->
  Indices ->
  ErrorEnv Tensor
dynamicUpdateSlice to update start = do
  t <- tensor to
  u <- tensor update
  genericApplyBinary (\t u -> Typed.dynamicUpdateSlice t u start) t u

dot ::
  (TensorOperand t1, TensorOperand t2) =>
  t1 ->
  t2 ->
  Indices ->
  Axes ->
  ErrorEnv Tensor
dot t1 t2 axes dims = do
  t1' <- tensor t1
  t2' <- tensor t2
  applyValBinary
    (\i1 i2 -> Typed.dot i1 i2 axes dims)
    (\i1 i2 -> Typed.dot i1 i2 axes dims)
    t1'
    t2'

convBase ::
  (TensorOperand t1, TensorOperand t2) =>
  t1 ->
  t2 ->
  ConvConfigArgs ->
  ErrorEnv Tensor
convBase inputo weightso baseConfig = do
  input <- tensor inputo
  weights <- tensor weightso
  applyValBinary
    (\i w -> Typed.convBase i w baseConfig)
    (\i w -> Typed.convBase i w baseConfig)
    input
    weights

conv ::
  (TensorOperand t1, TensorOperand t2) =>
  t1 ->
  t2 ->
  ConvConfigArgs ->
  ConvPaddingArgs ->
  ErrorEnv Tensor
conv inputo weightso baseConfig paddingConfig = do
  input <- tensor inputo
  weights <- tensor weightso
  applyValBinary
    (\i w -> Typed.conv i w baseConfig paddingConfig)
    (\i w -> Typed.conv i w baseConfig paddingConfig)
    input
    weights

clamp ::
  (TensorOperand t, TensorOperand tmin, TensorOperand tmax) =>
  tmin ->
  t ->
  tmax ->
  ErrorEnv Tensor
clamp mino to maxo = do
  min <- tensor mino
  t <- tensor to
  max <- tensor maxo
  case (min, t, max) of
    (IntTensor min', IntTensor t', IntTensor max') -> do
      r <- Typed.clamp min' t' max'
      mrgReturn $ IntTensor r
    (RealTensor min', RealTensor t', RealTensor max') -> do
      r <- Typed.clamp min' t' max'
      mrgReturn $ RealTensor r
    _ -> mrgThrowError "clamp: only valid for IntTensors or RealTensors"

clampScalar ::
  (TensorOperand t) =>
  Elem ->
  t ->
  Elem ->
  ErrorEnv Tensor
clampScalar low to high = do
  t <- tensor to
  case (t, low, high) of
    ( IntTensor t',
      IntElem (Typed.TensorElemVal low'),
      IntElem (Typed.TensorElemVal high')
      ) -> do
        r <- Typed.clampScalar low' t' high'
        mrgReturn $ IntTensor r
    ( RealTensor t',
      RealElem (Typed.TensorElemVal low'),
      RealElem (Typed.TensorElemVal high')
      ) -> do
        r <- Typed.clampScalar low' t' high'
        mrgReturn $ RealTensor r
    _ -> mrgThrowError "clampScalar: only valid for IntTensors"

reverseTensor ::
  (TensorOperand t) =>
  t ->
  Axes ->
  ErrorEnv Tensor
reverseTensor to axes =
  genericApplyUnary (`Typed.reverseTensor` axes) =<< tensor to

select ::
  (TensorOperand tpred, TensorOperand ttrue, TensorOperand tfalse) =>
  tpred ->
  ttrue ->
  tfalse ->
  ErrorEnv Tensor
select pred true false = do
  p <- tensor pred
  t <- tensor true
  f <- tensor false
  case p of
    (BoolTensor p') -> genericApplyBinary (Typed.select p') t f
    _ -> mrgThrowError "select: type mismatch"

reshapeDegenerate ::
  (TensorOperand t) =>
  t ->
  Axes ->
  Axes ->
  ErrorEnv Tensor
reshapeDegenerate to fromAxes toAxes = do
  t <- tensor to
  genericApplyUnary (\t -> Typed.reshapeDegenerate t fromAxes toAxes) t

numTensorAssumption ::
  (TensorOperand t) =>
  [t] ->
  Indices ->
  (forall v. (IsTensorNum v) => [TensorNum v] -> SymBool) ->
  ErrorEnv SymBool
numTensorAssumption ts i f = do
  ts' <- mapM tensor ts
  case extractAllIntTensor ts' of
    Just its -> Typed.tensorAssumption its i f
    _ -> case extractAllRealTensor ts' of
      Just rts -> Typed.tensorAssumption rts i f
      _ -> mrgThrowError "numTensorAssumption: type mismatch"
  where
    extractAllIntTensor :: [Tensor] -> Maybe [Typed.Tensor TensorInt]
    extractAllIntTensor [] = Just []
    extractAllIntTensor (IntTensor t : ts) = do
      ts' <- extractAllIntTensor ts
      return $ t : ts'
    extractAllIntTensor _ = Nothing
    extractAllRealTensor :: [Tensor] -> Maybe [Typed.Tensor TensorReal]
    extractAllRealTensor [] = Just []
    extractAllRealTensor (RealTensor t : ts) = do
      ts' <- extractAllRealTensor ts
      return $ t : ts'
    extractAllRealTensor _ = Nothing
