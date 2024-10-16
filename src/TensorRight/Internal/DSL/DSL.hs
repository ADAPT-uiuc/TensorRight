{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module TensorRight.Internal.DSL.DSL
  ( AdimRef (..),
    NumBinOp (..),
    BoolBinOp (..),
    NumUnaryOp (..),
    BoolUnaryOp (..),
    CompareOp (..),
    DType (..),
    Params,
    Expr,
    Env (..),
    DSLContext,
    intElem,
    boolElem,
    runDSLContext,
    newAdim,
    newMap,
    newNonNegMap,
    newNonNegMaps,
    newAdims,
    newMaps,
    newTensor,
    numBinOp,
    boolBinOp,
    reduce,
    siRelation,
    precondition,
    siRelation',
    precondition',
    broadcast,
    compareOp,
    constant,
    iota,
    slice,
    pad,
    relabel,
    dynamicSlice,
    dynamicUpdateSlice,
    concatTensor,
    concatTensorList,
    dot,
    numBinScalarOp,
    boolBinScalarOp,
    numUnaryOp,
    boolUnaryOp,
    convBase,
    conv,
    monitorExprOnFailure,
    monitorMapOnFailure,
    clamp,
    clampScalar,
    select,
    reverseTensor,
    sumMap,
    newConstMap,
    newConstMaps,
    combineMap,
    Padding (..),
    ConvConfig (..),
    ConvPadding (..),
    Slice (..),
    DySlice (..),
    ValidElem,
    ValidNum,
    AnyDTypeRule,
    NumRule,
    checkSIMap,
    reshapeDegenerate,
    numTensorAssumption,
  )
where

import Control.Monad (foldM)
import Control.Monad.Except (MonadError (throwError))
import Control.Monad.State (MonadState (get, put), modify)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.String (IsString)
import qualified Data.Text as T
import Grisette
  ( Mergeable,
    SymBool,
    SymEq ((.==)),
    SymInteger,
    SymOrd ((.>=)),
  )
import Grisette.Lib.Control.Monad.Except (mrgThrowError)
import TensorRight.Internal.Core.Tensor
  ( BoolBinOp (And, Or),
    DType (BoolType, IntType, RealType),
    Elem (BoolElem, IntElem, RealElem),
    NumBinOp (Add, Mul),
    ToDType (toDType),
    ToElem (toElem),
  )
import TensorRight.Internal.Core.Tensor.TensorInt (TensorInt, TensorNum, TensorReal, IsTensorNum)
import TensorRight.Internal.Core.Tensor.Typed (BoolUnaryOp, CompareOp, NumUnaryOp)
import qualified TensorRight.Internal.Core.Tensor.Typed as Typed
import TensorRight.Internal.DSL.Condition (Condition (Condition), zipCondition)
import TensorRight.Internal.DSL.Expr
  ( ConvConfigArgsExpr
      ( ConvConfigArgsExpr,
        batchAdims,
        contractingSIMaps,
        featureAdims,
        outputFeatureAdims,
        strides
      ),
    ConvPaddingArgsExpr (ConvPaddingArgsExpr, high, ldilation, low, rdilation),
    DSLContext,
    DySliceArgsExpr (DySliceArgsExpr, sizes, start),
    Env (Env, lhsSIMaps, numTensorAssumptions),
    Expr,
    NumTensorAssumption (NumTensorAssumption),
    PaddingArgsExpr (PaddingArgsExpr, high, interior, low),
    Params,
    Rewrite,
    SliceArgsExpr (SliceArgsExpr, end, start, strides),
    UExpr
      ( UBoolBinOp,
        UBoolScalarBinOp,
        UBoolUnaryOp,
        UBroadcast,
        UClamp,
        UClampScalar,
        UCompareOp,
        UConcat,
        UConcatList,
        UConstant,
        UConv,
        UConvBase,
        UDot,
        UDynamicSlice,
        UDynamicUpdateSlice,
        UIota,
        UNumBinOp,
        UNumScalarBinOp,
        UNumUnaryOp,
        UPad,
        UReduce,
        URelabel,
        UReshapeDegenerate,
        UReverseTensor,
        USelect,
        USlice,
        UVar
      ),
    checkParamsWellFormed,
    declaredAdims,
    exprAbstractShapes,
    exprDTypes,
    exprId,
    exprs,
    getAdimByMap,
    internExpr,
    internWithCheck,
    lhsSIMaps,
    mapAdims,
    monitorExprOnFailure,
    monitorMapOnFailure,
    preConditions,
    rhsSIMaps,
    runDSLContext,
    siRelations,
    singletonAdims,
    tensorDTypes,
    tensorShapes,
    validTensorShape,
  )
import TensorRight.Internal.DSL.Identifier
  ( AdimIdentifier,
    Identifier (SimpleIdentifier),
    MapIdentifier,
    nextIdentifier,
  )
import TensorRight.Internal.DSL.Parameters (IsParamMaps (toParamMaps), ParamDesc)
import TensorRight.Internal.DSL.RelabelMap (IsRelabelMap (toRelabelMap), RelabelMapDesc)
import TensorRight.Internal.DSL.Shape
  ( AbstractShape (AbstractShape, labelled, unlabelled),
    AdimRef (ByAdim, ByLabel),
    TensorShapeDesc,
    TensorShapeLike (toTensorShape),
    abstractShapeAllRefs,
    addAdimByAdimRef,
    concatAbstractShape,
    getAdimByAdimRef,
    removeAdim,
    restrictAbstractShape,
    toAbstractShape,
  )
import TensorRight.Internal.Util.Error (assert)

-- | Create an integer element from a tensor int.
intElem :: TensorInt -> Elem
intElem = IntElem . Typed.TensorElemVal

-- | Create a boolean element from a symbolic boolean.
boolElem :: SymBool -> Elem
boolElem = BoolElem . Typed.TensorElemVal

shapeOf :: Expr -> DSLContext AbstractShape
shapeOf expr = do
  env <- get
  return $ exprAbstractShapes env HM.! exprId expr

typeOf :: Expr -> DSLContext DType
typeOf expr = do
  env <- get
  return $ exprDTypes env HM.! exprId expr

shapeAndTypeOf :: Expr -> DSLContext (AbstractShape, DType)
shapeAndTypeOf expr = do
  shape <- shapeOf expr
  ty <- typeOf expr
  return (shape, ty)

-- | Create an adim with a given name. The name doesn't have to be unique.
-- TensorRight will rename them.
newAdim :: T.Text -> DSLContext AdimIdentifier
newAdim name = do
  env <- get
  let adim = augment (declaredAdims env) $ SimpleIdentifier name
  put $ env {declaredAdims = HS.insert adim (declaredAdims env)}
  return adim
  where
    augment declaredAdims ident =
      if HS.member ident declaredAdims
        then augment declaredAdims $ nextIdentifier ident
        else ident

-- | Create a list of adim with a list of names. The names don't have to be
-- unique. TensorRight will rename them.
newAdims :: [T.Text] -> DSLContext [AdimIdentifier]
newAdims = traverse newAdim

-- | Create a new map for a given adim. The map can be used as sizes or indices.
newMap :: T.Text -> AdimIdentifier -> DSLContext MapIdentifier
newMap name adim = do
  env <- get
  let mapId = augment (mapAdims env) $ SimpleIdentifier name
  put $ env {mapAdims = HM.insert mapId adim (mapAdims env)}
  return mapId
  where
    augment mapAdims ident =
      if HM.member ident mapAdims
        then augment mapAdims $ nextIdentifier ident
        else ident

-- | Create a list of maps for a given adim. The maps can be used as sizes or
-- indices.
newMaps :: [T.Text] -> AdimIdentifier -> DSLContext [MapIdentifier]
newMaps names adim = traverse (`newMap` adim) names

-- | Create a new map for a given map. The map can be used as sizes or indices.
-- The contents of the map are assumed to be non-negative.
newNonNegMap :: T.Text -> AdimIdentifier -> DSLContext MapIdentifier
newNonNegMap name adim = do
  map <- newMap name adim
  precondition [map] $ \[m] -> m .>= 0
  return map

-- | Create a list of maps for a given adim. The maps can be used as sizes or
-- indices. The contents of the maps are assumed to be non-negative.
newNonNegMaps :: [T.Text] -> AdimIdentifier -> DSLContext [MapIdentifier]
newNonNegMaps names adim = traverse (`newNonNegMap` adim) names

-- | Create a new map for a given map. The map can be used as sizes or indices.
-- The contents of the map are assumed to be a specific constant number.
newConstMap :: T.Text -> SymInteger -> AdimIdentifier -> DSLContext MapIdentifier
newConstMap name c adim = do
  map <- newMap name adim
  precondition [map] $ \[m] -> m .== c
  return map

-- | Create a list of maps for a given adim. The maps can be used as sizes or
-- indices. The contents of the maps are assumed to be a specific constant
-- number.
newConstMaps :: [T.Text] -> SymInteger -> AdimIdentifier -> DSLContext [MapIdentifier]
newConstMaps names c adim = traverse (\name -> newConstMap name c adim) names

-- | Create a new map where its contents are the sum of the contents of the
-- provided maps. The maps must have the same adim.
sumMap :: T.Text -> [MapIdentifier] -> DSLContext MapIdentifier
sumMap name = combineMap name sum

-- | Create a new map where its contents are the combination of the contents of
-- the provided maps. The maps must have the same adim.
--
-- The combination is done with a function.
combineMap ::
  T.Text ->
  ([SymInteger] -> SymInteger) ->
  [MapIdentifier] ->
  DSLContext MapIdentifier
combineMap _ _ [] = throwError "Cannot combine an empty list of maps"
combineMap name f (m : maps) = do
  adim <- getAdimByMap m
  adims <- traverse getAdimByMap maps
  assert "All maps must have the same adim" $ all (== adim) adims
  r <- newMap name adim
  precondition (r : m : maps) $ \(r' : ms) -> r' .== f ms
  return r

numTensorAssumption ::
  [Expr] ->
  MapIdentifier ->
  (forall v. (IsTensorNum v) => [TensorNum v] -> SymBool) ->
  DSLContext ()
numTensorAssumption tensors map f = do
  env <- get
  put $
    env
      { numTensorAssumptions =
          NumTensorAssumption tensors map f : numTensorAssumptions env
      }

-- | Add a precondition to rewriting rule.
precondition' ::
  [MapIdentifier] ->
  ([HM.HashMap T.Text SymInteger] -> SymBool) ->
  DSLContext ()
precondition' maps condition = do
  env <- get
  put $ env {preConditions = Condition maps condition : preConditions env}

-- | Add a precondition to rewriting rule.
precondition ::
  [MapIdentifier] ->
  ([SymInteger] -> SymBool) ->
  DSLContext ()
precondition maps = precondition' maps . zipCondition

-- | Add an SI relation to rewriting rule.
siRelation' ::
  [MapIdentifier] ->
  ([HM.HashMap T.Text SymInteger] -> SymBool) ->
  DSLContext ()
siRelation' maps condition = do
  env <- get
  put $ env {siRelations = Condition maps condition : siRelations env}

-- | Add an SI relation to rewriting rule.
siRelation ::
  [MapIdentifier] ->
  ([SymInteger] -> SymBool) ->
  DSLContext ()
siRelation maps = siRelation' maps . zipCondition

-- | Create a new tensor with a given name, dtype, and shape.
newTensor ::
  forall a.
  (ToDType a) =>
  -- | Name
  T.Text ->
  -- | Shape, e.g., [adim --> map] or [adim --> map, adim1 --> map1 @@ label]
  [TensorShapeDesc] ->
  DSLContext Expr
newTensor name shapeLike = do
  let dtype = toDType (undefined :: a)
  shape <- toTensorShape shapeLike
  validTensorShape shape
  env <- get
  let tensorId = augment (tensorShapes env) $ SimpleIdentifier name
  put $
    env
      { tensorShapes = HM.insert tensorId shape (tensorShapes env),
        tensorDTypes = HM.insert tensorId dtype (tensorDTypes env)
      }
  internExpr (UVar tensorId) (toAbstractShape shape) dtype
  where
    augment tensorShapes ident =
      if HM.member ident tensorShapes
        then augment tensorShapes $ nextIdentifier ident
        else ident

class ExprInContext e where
  liftInContext :: e -> DSLContext Expr

instance ExprInContext Expr where
  liftInContext = return

instance ExprInContext (DSLContext Expr) where
  liftInContext = id

-- | Number binary operation. The lhs and rhs must have the same shape, and
-- the dtype of lhs and rhs must be 'IntType' or 'RealType'.
numBinOp ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | Integer binary operator.
  NumBinOp ->
  -- | Lhs expression.
  lhs ->
  -- | Rhs expression.
  rhs ->
  DSLContext Expr
numBinOp op lhs' rhs' = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  internWithCheck (UNumBinOp op lhs rhs) $ do
    shapeLhs <- shapeOf lhs
    shapeRhs <- shapeOf rhs
    typeLhs <- typeOf lhs
    typeRhs <- typeOf rhs
    assert "Shapes do not match" $ shapeLhs == shapeRhs
    assert "lhs must be int or real" $ typeLhs `elem` [IntType, RealType]
    assert "lhs and rhs must have the same dtype" $ typeLhs == typeRhs
    return (shapeLhs, typeLhs)

-- | Number binary operation with a scalar. The dtype of lhs must be 'IntType'
-- or 'RealType'.
numBinScalarOp ::
  (ToElem a, ToDType a, ExprInContext lhs) =>
  -- | Integer binary operator.
  NumBinOp ->
  -- | Lhs expression.
  lhs ->
  -- | Rhs scalar.
  a ->
  DSLContext Expr
numBinScalarOp op lhs' rhs = do
  lhs <- liftInContext lhs'
  internWithCheck (UNumScalarBinOp op lhs (toElem rhs)) $ do
    shapeLhs <- shapeOf lhs
    typeLhs <- typeOf lhs
    assert "lhs must be int or real" $ typeLhs `elem` [IntType, RealType]
    assert "lhs and rhs must have the same dtype" $ toDType rhs == typeLhs
    return (shapeLhs, IntType)

-- | Boolean binary operation. The lhs and rhs must have the same shape, and
-- the dtype of lhs and rhs must be 'BoolType'.
boolBinOp ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | Boolean binary operator.
  BoolBinOp ->
  -- | Lhs expression.
  lhs ->
  -- | Rhs expression.
  rhs ->
  DSLContext Expr
boolBinOp op lhs' rhs' = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  internWithCheck (UBoolBinOp op lhs rhs) $ do
    shapeLhs <- shapeOf lhs
    shapeRhs <- shapeOf rhs
    typeLhs <- typeOf lhs
    typeRhs <- typeOf rhs
    assert "Shapes do not match" $ shapeLhs == shapeRhs
    assert "lhs must be bool" $ typeLhs == BoolType
    assert "rhs must be bool" $ typeRhs == BoolType
    return (shapeLhs, BoolType)

-- | Boolean binary operation with a scalar. The dtype of lhs must be
-- 'BoolType'.
boolBinScalarOp ::
  (ExprInContext lhs) =>
  -- | Boolean binary operator.
  BoolBinOp ->
  -- | Lhs expression.
  lhs ->
  -- | Rhs scalar.
  SymBool ->
  DSLContext Expr
boolBinScalarOp op lhs' rhs = do
  lhs <- liftInContext lhs'
  internWithCheck (UBoolScalarBinOp op lhs rhs) $ do
    shapeLhs <- shapeOf lhs
    typeLhs <- typeOf lhs
    assert "lhs must be bool" $ typeLhs == BoolType
    return (shapeLhs, BoolType)

-- | Compare operation. The lhs and rhs must have the same shape, and the dtype
-- of lhs and rhs must be 'IntType' or 'RealType'. The result of the comparison
-- is a boolean.
compareOp ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | Compare operator.
  CompareOp ->
  -- | Lhs expression.
  lhs ->
  -- | Rhs expression.
  rhs ->
  DSLContext Expr
compareOp op lhs' rhs' = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  internWithCheck (UCompareOp op lhs rhs) $ do
    shapeLhs <- shapeOf lhs
    shapeRhs <- shapeOf rhs
    typeLhs <- typeOf lhs
    typeRhs <- typeOf rhs
    assert "Shapes do not match" $ shapeLhs == shapeRhs
    assert "lhs must be int or real" $ typeLhs `elem` [IntType, RealType]
    assert "lhs and rhs must have the same dtype" $ typeLhs == typeRhs
    return (shapeLhs, BoolType)

-- | Number unary operation. The expression must have the dtype 'IntType' or
-- 'RealType'.
numUnaryOp ::
  (ExprInContext e) =>
  NumUnaryOp ->
  e ->
  DSLContext Expr
numUnaryOp op expr' = do
  expr <- liftInContext expr'
  internWithCheck (UNumUnaryOp op expr) $ do
    shape <- shapeOf expr
    type' <- typeOf expr
    assert "Expression must be int or real" $ type' `elem` [IntType, RealType]
    return (shape, type')

-- | Boolean unary operation. The expression must have the dtype 'BoolType'.
boolUnaryOp ::
  (ExprInContext e) =>
  BoolUnaryOp ->
  e ->
  DSLContext Expr
boolUnaryOp op expr' = do
  expr <- liftInContext expr'
  internWithCheck (UBoolUnaryOp op expr) $ do
    shape <- shapeOf expr
    type' <- typeOf expr
    assert "Expression must be bool" $ type' == BoolType
    return (shape, BoolType)

-- | Reduce operation. The expression must have the dtype 'IntType'.
--
-- The description of the si-indices (i.e., the @'ParamDesc'@), can either be
-- @<adim> '-->' <map>@ or @ByLabel <label> '-->' <map>@.
--
-- Each sum index specifies the adim to be reduced and the map to be used for
-- the si-indices. This can be done by either providing an 'Adim' identifier, or
-- a label.
--
-- Note that the reference needs to be @'ByLabel' <label>@ for labelled @Adims@,
-- or an @<adim>@ otherwise. This is different from 'TensorShapeDesc', where you
-- need to provide the labels with the @Adim@.
reduce ::
  (ExprInContext e) =>
  -- | The expression to perform the reduction on.
  e ->
  -- | The description of the si-indices.
  [ParamDesc] ->
  DSLContext Expr
reduce expr' m = do
  expr <- liftInContext expr'
  let siMap = toParamMaps m
  internWithCheck (UReduce expr siMap) $ do
    shape <- shapeOf expr
    ty <- typeOf expr
    assert "Expression must be int or real" $ ty `elem` [IntType, RealType]
    checkParamsWellFormed shape siMap
    reducedShape <- foldM removeAdim shape $ HM.keys siMap
    return (reducedShape, ty)

-- | Broadcast operation.
broadcast ::
  (ExprInContext e) =>
  -- | Tensor to broadcast.
  e ->
  -- | The shape to broadcast to. It should be disjoint from the shape of the
  -- input tensor.
  [TensorShapeDesc] ->
  DSLContext Expr
broadcast expr' extendedShape = do
  expr <- liftInContext expr'
  eshape <- toTensorShape extendedShape
  internWithCheck (UBroadcast expr eshape) $ do
    shape <- shapeOf expr
    ty <- typeOf expr
    validTensorShape eshape
    broadcastedShape <- concatAbstractShape (toAbstractShape eshape) shape
    return (broadcastedShape, ty)

-- | Constant tensor operation.
constant ::
  (ToElem a, ToDType a) =>
  -- | The value. The resulting tensor will have the same value at all indices.
  a ->
  -- | The shape of the tensor.
  [TensorShapeDesc] ->
  DSLContext Expr
constant i shapeDesc = do
  shape <- toTensorShape shapeDesc
  validTensorShape shape
  internExpr (UConstant (toElem i) shape) (toAbstractShape shape) (toDType i)

checkParamsCoverAbstractShape :: AbstractShape -> Params -> DSLContext ()
checkParamsCoverAbstractShape AbstractShape {..} params = do
  let foldingFunc ref (l, u) = case ref of
        ByAdim adim -> (l, adim : u)
        ByLabel label -> (label : l, u)
  let (labels, adims) = HS.foldr foldingFunc ([], []) $ HM.keysSet params
  assert "Incorrect labels provided in parameters" $ HS.fromList labels == HM.keysSet labelled
  assert "Incorrect adims provided in parameters" $ HS.fromList adims == unlabelled

-- | Iota operation.
iota ::
  -- | The shape of the tensor.
  [TensorShapeDesc] ->
  -- | The @Adim@ along which the tensor values increment by one.
  AdimRef ->
  DSLContext Expr
iota shapeDesc d = do
  shape <- toTensorShape shapeDesc
  internWithCheck (UIota shape d) $ do
    validTensorShape shape
    let abstractShape = toAbstractShape shape
    adim <- getAdimByAdimRef abstractShape d
    env <- get
    put $ env {singletonAdims = HS.insert adim (singletonAdims env)}
    return (abstractShape, IntType)

-- | The named arguments to the 'slice' operation.
data Slice = Slice
  { start :: [ParamDesc],
    end :: [ParamDesc],
    strides :: [ParamDesc]
  }

class SliceFun a where
  type SliceRes a

  -- | Slice operation.
  --
  -- Either
  --
  -- @
  -- slice tensor $
  --   Slice {
  --     start = [adim --> startMap],
  --     end = [adim --> map],
  --     strides = [adim --> map]
  --   }
  -- @
  --
  -- or
  --
  -- @
  -- slice tensor [adim --> startMap] [adim --> endMap] [adim --> strideMap]
  -- @
  slice ::
    (ExprInContext e) =>
    -- | The tensor to slice.
    e ->
    -- | The next argument. Could be a 'Slice', and return a
    -- @'DSLContext' 'Expr'@, or it could be three @['ParamDesc']@, without the
    -- names. We recommend using named arguments all the time.
    a ->
    SliceRes a

instance SliceFun Slice where
  type SliceRes Slice = DSLContext Expr
  slice = sliceImpl

instance (a ~ ParamDesc) => SliceFun [a] where
  type SliceRes [a] = [ParamDesc] -> [ParamDesc] -> DSLContext Expr
  slice e start end strides = sliceImpl e $ Slice {..}

sliceImpl ::
  (ExprInContext e) =>
  e ->
  Slice ->
  DSLContext Expr
sliceImpl expr' Slice {..} = do
  expr <- liftInContext expr'
  let ms = toParamMaps start
      me = toParamMaps end
      mp = toParamMaps strides
  internWithCheck
    (USlice expr $ SliceArgsExpr {start = ms, end = me, strides = mp})
    $ do
      shape <- shapeOf expr
      ty <- typeOf expr
      assert "start must have the same Adims as end" $ HM.keysSet ms == HM.keysSet me
      assert "start must have the same Adims as strides" $ HM.keysSet ms == HM.keysSet mp
      checkParamsWellFormed shape ms
      checkParamsWellFormed shape me
      checkParamsWellFormed shape mp
      -- Check if the AdimRefs are in the tensor shape
      -- We are allowed to slice a part of the adims
      mapM_ (getAdimByAdimRef shape) $ HM.keys ms
      return (shape, ty)

-- | The named arguments to the 'pad' operation.
data Padding = Padding
  { low :: [ParamDesc],
    interior :: [ParamDesc],
    high :: [ParamDesc]
  }

padCheck ::
  (AbstractShape, DType) ->
  Elem ->
  Padding ->
  DSLContext (AbstractShape, DType)
padCheck (shape, ty) elem Padding {..} = do
  -- Check if the padding element has the same type as the tensor
  assert "Padding element must have the same type as the tensor" $
    case elem of
      RealElem _ -> ty == RealType
      IntElem _ -> ty == IntType
      BoolElem _ -> ty == BoolType
  let l = toParamMaps low
      i = toParamMaps interior
      h = toParamMaps high
  checkParamsWellFormed shape l
  checkParamsWellFormed shape i
  checkParamsWellFormed shape h
  return (shape, ty)

class PaddingFun a where
  type PaddingRes a

  -- | Pad operation.
  --
  -- Either
  --
  -- @
  -- pad tensor (intElem 0) $
  --   Padding {
  --     low = [adim --> lowMap],
  --     interior = [adim --> intMap],
  --     high = [adim --> highMap]
  --   }
  -- @
  --
  -- or
  --
  -- @
  -- pad tensor (intElem 0) [adim --> lowMap] [adim --> intMap] [adim --> highMap]
  -- @
  pad ::
    (ExprInContext e, ToElem v, ToDType v) =>
    -- | The tensor to pad.
    e ->
    -- | The element to pad. Usually created with 'intElem' or 'boolElem'.
    v ->
    -- | The next argument. Could be a 'Padding', and return a
    -- @'DSLContext' 'Expr'@, or it could be three @['ParamDesc']@, without the
    -- names. We recommend using named arguments all the time.
    a ->
    PaddingRes a

instance PaddingFun Padding where
  type PaddingRes Padding = DSLContext Expr
  pad = padImpl

instance (a ~ ParamDesc) => PaddingFun [a] where
  type PaddingRes [a] = [ParamDesc] -> [ParamDesc] -> DSLContext Expr
  pad e elem low int high = padImpl e elem $ Padding low int high

-- | Named arguments to the 'convBase' and 'conv' operation.
data ConvConfig = ConvConfig
  { batchAdims :: [AdimRef],
    featureAdims :: [AdimRef],
    outputFeatureAdims :: [AdimRef],
    strides :: [ParamDesc],
    contractingSIMaps :: [ParamDesc]
  }

class ConvBaseFun a where
  type ConvBaseRes a

  -- | Convolution base operation. No padding is applied.
  --
  -- Either
  --
  -- @
  -- convBase input weights $
  --   ConvConfig {
  --     batchAdims = [ByAdim batch],
  --     featureAdims = [ByAdim feature],
  --     outputFeatureAdims = [ByAdim outputFeature],
  --     strides = [adim --> strideMap],
  --     contractingSIMaps = [adim --> siMap]
  --   }
  -- @
  --
  -- or
  --
  -- @
  -- convBase
  --   input
  --   weights
  --   [ByAdim batch]
  --   [ByAdim feature]
  --   [ByAdim outputFeature]
  --   [adim --> strideMap]
  --   [adim --> siMap]
  -- @
  convBase ::
    (ExprInContext input, ExprInContext weights) =>
    -- | The input tensor.
    input ->
    -- | The weights (kernel) tensor.
    weights ->
    -- | The next argument. Could be a 'ConvConfig', and return a
    -- @'DSLContext' 'Expr'@, or it could be
    -- @['AdimRef'] -> ['AdimRef'] -> ['AdimRef'] -> ['ParamDesc'] -> ['ParamDesc'] -> 'DSLContext' 'Expr'@,
    -- without the names. We recommend using named arguments all the time.
    a ->
    ConvBaseRes a

instance ConvBaseFun ConvConfig where
  type ConvBaseRes ConvConfig = DSLContext Expr
  convBase = convBaseImpl

instance (a ~ AdimRef) => ConvBaseFun [a] where
  type
    ConvBaseRes [a] =
      [AdimRef] -> [AdimRef] -> [ParamDesc] -> [ParamDesc] -> DSLContext Expr
  convBase input weights batch feature outputFeatureAdims strides siMaps =
    convBaseImpl input weights $
      ConvConfig batch feature outputFeatureAdims strides siMaps

-- | Padding for the 'conv' operation.
data ConvPadding = ConvPadding
  { low :: [ParamDesc],
    ldilation :: [ParamDesc],
    high :: [ParamDesc],
    rdilation :: [ParamDesc]
  }

class ConvFun a where
  type ConvRes a

  -- | Convolution operation.
  -- The input tensor and the weights tensor must have the same dtype.
  --
  -- Either
  --
  -- @
  -- conv input weights $
  --   ConvConfig {
  --     batchAdims = [ByAdim batch],
  --     featureAdims = [ByAdim feature],
  --     outputFeatureAdims = [ByAdim outputFeature],
  --     strides = [adim --> strideMap],
  --     contractingSIMaps = [adim --> siMap]
  --   }
  --   ConvPadding {
  --     low = [adim --> lowMap],
  --     ldilation = [adim --> ldilationMap],
  --     high = [adim --> highMap],
  --     rdilation = [adim --> rdilationMap]
  --   }
  -- @
  --
  -- or use unnamed arguments. We do not recommend that.
  conv ::
    (ExprInContext input, ExprInContext weights) =>
    -- | The input tensor.
    input ->
    -- | The weights (kernel) tensor.
    weights ->
    a ->
    ConvRes a

instance ConvFun ConvConfig where
  type ConvRes ConvConfig = ConvPadding -> DSLContext Expr
  conv = convImpl

instance (a ~ AdimRef) => ConvFun [a] where
  type
    ConvRes [a] =
      [AdimRef] ->
      [AdimRef] ->
      [ParamDesc] ->
      [ParamDesc] ->
      [ParamDesc] ->
      [ParamDesc] ->
      [ParamDesc] ->
      [ParamDesc] ->
      DSLContext Expr

  conv
    input
    weights
    batch
    feature
    outputFeatureAdims
    strides
    siMaps
    low
    ldilation
    high
    rdilation =
      convImpl
        input
        weights
        (ConvConfig batch feature outputFeatureAdims strides siMaps)
        (ConvPadding low ldilation high rdilation)

padImpl ::
  (ToElem a, ToDType a, ExprInContext e) =>
  e ->
  a ->
  Padding ->
  DSLContext Expr
padImpl expr' elem padding@Padding {..} = do
  expr <- liftInContext expr'
  let l = toParamMaps low
      i = toParamMaps interior
      h = toParamMaps high
  internWithCheck
    (UPad expr (toElem elem) $ PaddingArgsExpr {low = l, interior = i, high = h})
    $ do
      shapeAndTy@(_, tdty) <- shapeAndTypeOf expr
      let ety = toDType elem
      assert "Element must have the same type as the tensor" $ tdty == ety
      padCheck shapeAndTy (toElem elem) padding

-- | Named arguments to the 'dynamicSlice' operation.
data DySlice = DySlice
  { start :: [ParamDesc],
    sizes :: [ParamDesc]
  }

class DySliceFun a where
  type DySliceRes a

  -- | Dynamic slice operation.
  --
  -- Either
  --
  -- @
  -- dynamicSlice tensor $
  --   DySlice {
  --     start = [adim --> startMap],
  --     sizes = [adim --> sizeMap]
  --  }
  -- @
  --
  -- or
  --
  -- @
  -- dynamicSlice tensor [adim --> startMap] [adim --> sizeMap]
  -- @
  dynamicSlice :: (ExprInContext e) => e -> a -> DySliceRes a

instance DySliceFun DySlice where
  type DySliceRes DySlice = DSLContext Expr
  dynamicSlice = dynamicSliceImpl

instance (a ~ ParamDesc) => DySliceFun [a] where
  type DySliceRes [a] = [ParamDesc] -> DSLContext Expr
  dynamicSlice e start sizes = dynamicSliceImpl e $ DySlice {..}

dynamicSliceImpl ::
  (ExprInContext e) =>
  e ->
  DySlice ->
  DSLContext Expr
dynamicSliceImpl expr' DySlice {..} = do
  expr <- liftInContext expr'
  let s = toParamMaps start
      z = toParamMaps sizes
  internWithCheck (UDynamicSlice expr $ DySliceArgsExpr {start = s, sizes = z}) $ do
    shape <- shapeOf expr
    ty <- typeOf expr
    assert "start must have the same Adims as sizes" $ HM.keysSet s == HM.keysSet z
    checkParamsWellFormed shape s
    checkParamsWellFormed shape z
    -- Check if the AdimRefs are in the tensor shape
    -- We are allowed to slice a part of the adims
    mapM_ (getAdimByAdimRef shape) $ HM.keys s
    return (shape, ty)

-- | Dynamic update slice operation.
dynamicUpdateSlice ::
  (ExprInContext t, ExprInContext u) =>
  -- | The tensor to update.
  t ->
  -- | The update tensor.
  u ->
  -- | The start indices.
  [ParamDesc] ->
  DSLContext Expr
dynamicUpdateSlice expr' update' start = do
  expr <- liftInContext expr'
  update <- liftInContext update'
  let s = toParamMaps start
  internWithCheck (UDynamicUpdateSlice expr update s) $ do
    shape <- shapeOf expr
    ty <- typeOf expr
    updateShape <- shapeOf update
    updateTy <- typeOf update
    assert "update must have the same adims as original" $ shape == updateShape
    assert "update must have the same type as original" $ ty == updateTy
    checkParamsWellFormed shape s
    -- The adim refs in the start params must cover the tensor shape
    checkParamsCoverAbstractShape shape s
    return (shape, ty)

-- | Concatenate operation.
concatTensor ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The left-hand side tensor.
  lhs ->
  -- | The right-hand side tensor.
  rhs ->
  -- | The adim to concat on.
  AdimRef ->
  DSLContext Expr
concatTensor lhs' rhs' d = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  internWithCheck (UConcat lhs rhs d) $ do
    shapeLhs <- shapeOf lhs
    shapeRhs <- shapeOf rhs
    tyLhs <- typeOf lhs
    tyRhs <- typeOf rhs
    assert "lhs and rhs must have the same adims" $ shapeLhs == shapeRhs
    assert "lhs and rhs must have the same type" $ tyLhs == tyRhs
    adim <- getAdimByAdimRef shapeLhs d
    env <- get
    put $ env {singletonAdims = HS.insert adim (singletonAdims env)}
    return (shapeLhs, tyLhs)

-- | Concatenate a list of tensors.
concatTensorList ::
  (ExprInContext e) =>
  -- | The list of tensors to concatenate.
  [e] ->
  -- | The adim to concat on.
  AdimRef ->
  DSLContext Expr
concatTensorList exprs' d = do
  assert "concatTensorList cannot be empty" $ not $ null exprs'
  exprs <- traverse liftInContext exprs'
  internWithCheck (UConcatList exprs d) $ do
    shapes <- traverse shapeOf exprs
    tys <- traverse typeOf exprs
    assert "All tensors in concatList must have the same Adims" $ all (== head shapes) shapes
    assert "All tensors in concatList must have the same type" $ all (== head tys) tys
    adim <- getAdimByAdimRef (head shapes) d
    env <- get
    put $ env {singletonAdims = HS.insert adim (singletonAdims env)}
    return (head shapes, head tys)

-- | Relabel operation.
relabel ::
  (ExprInContext e) =>
  -- | The tensor to relabel.
  e ->
  -- | The relabel map. Should be @[adim --> 'ByLabel' label]@ or
  -- @['ByLabel' label -> 'ByLabel' label, ...]@.
  [RelabelMapDesc] ->
  DSLContext Expr
relabel expr' relabelMapDescs = do
  expr <- liftInContext expr'
  let relabelMap = toRelabelMap relabelMapDescs
  internWithCheck (URelabel expr relabelMap) $ do
    shape <- shapeOf expr
    let allRefs = abstractShapeAllRefs shape
    assert "the relabel map should be a subset of all axis" $
      HM.keysSet relabelMap `HS.isSubsetOf` allRefs
    let notRelabelledRefs = allRefs `HS.difference` HM.keysSet relabelMap
    let augmentedRelabelMap =
          relabelMap
            <> HM.fromList
              ((\ref -> (ref, ref)) <$> HS.toList notRelabelledRefs)
    assert "no two axes mapped to the same adim+label" $
      HS.size (HS.fromList $ HM.elems augmentedRelabelMap)
        == HM.size augmentedRelabelMap

    newShape <-
      foldM
        ( \newShape (from, to) -> do
            adim <- getAdimByAdimRef shape from
            addAdimByAdimRef newShape to adim
        )
        (AbstractShape HM.empty HS.empty)
        (HM.toList augmentedRelabelMap)
    ty <- typeOf expr
    return (newShape, ty)

-- | Dot operation.
dot ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The left-hand side tensor.
  lhs ->
  -- | The right-hand side tensor.
  rhs ->
  -- | The contracting SI maps.
  [ParamDesc] ->
  -- | The batch adims.
  [AdimRef] ->
  DSLContext Expr
dot lhs rhs contractingSIMapsDesc batchAdims = do
  lhs' <- liftInContext lhs
  rhs' <- liftInContext rhs
  let contractingSIMaps = toParamMaps contractingSIMapsDesc
  internWithCheck (UDot lhs' rhs' contractingSIMaps batchAdims) $ do
    shapeLhs <- shapeOf lhs'
    shapeRhs <- shapeOf rhs'
    tyLhs <- typeOf lhs'
    tyRhs <- typeOf rhs'
    assert "lhs must be integer or real type" $ tyLhs `elem` [IntType, RealType]
    assert "rhs must be the same as lhs type" $ tyRhs == tyLhs
    assert "Contracting and batch adims must be disjoint" $
      HS.null $
        HS.intersection (HS.fromList batchAdims) (HM.keysSet contractingSIMaps)
    let dotAllRefs = HM.keysSet contractingSIMaps <> HS.fromList batchAdims
    let lhsAllRefs = abstractShapeAllRefs shapeLhs
    let rhsAllRefs = abstractShapeAllRefs shapeRhs
    assert
      ( "Contracion + batch adims must be exactly the interaction of lhs and "
          <> "rhs adims"
      )
      $ dotAllRefs == HS.intersection lhsAllRefs rhsAllRefs
    checkParamsWellFormed shapeLhs contractingSIMaps
    lhsRemoved <- foldM removeAdim shapeLhs dotAllRefs
    rhsRemoved <- foldM removeAdim shapeRhs $ HM.keysSet contractingSIMaps
    finalShape <- concatAbstractShape lhsRemoved rhsRemoved
    return (finalShape, tyLhs)

convBaseCheck ::
  (AbstractShape, DType) ->
  (AbstractShape, DType) ->
  ConvConfig ->
  DSLContext (AbstractShape, DType)
convBaseCheck
  (shapeInput, tyInput)
  (shapeWeights, tyWeights)
  ConvConfig {..} = do
    let stridesMap = toParamMaps strides
        siMapsMap = toParamMaps contractingSIMaps
        batchAdimsSet = HS.fromList batchAdims
        featureAdimsSet = HS.fromList featureAdims
        outputFeatureAdimsSet = HS.fromList outputFeatureAdims
    assert "input must be int or real type" $ tyInput `elem` [IntType, RealType]
    assert "weights must be the same as input type" $ tyWeights == tyInput
    let inputAdims = abstractShapeAllRefs shapeInput
    let weightAdims = abstractShapeAllRefs shapeWeights
    assert "batch adims should be input adims - weight adims" $
      batchAdimsSet == inputAdims `HS.difference` weightAdims
    assert "output feature adims should be weight adims - input adims" $
      outputFeatureAdimsSet == weightAdims `HS.difference` inputAdims
    assert
      ( "input feature should be in the intersection of input and weight "
          <> "adims"
      )
      $ HS.isSubsetOf featureAdimsSet
      $ inputAdims `HS.intersection` weightAdims

    let inputAdims = abstractShapeAllRefs shapeInput
    let weightAdims = abstractShapeAllRefs shapeWeights
    assert "batch adims must be input axes - weight axes" $
      batchAdimsSet == inputAdims `HS.difference` weightAdims
    assert "output feature adims must be weight adims - input adims" $
      outputFeatureAdimsSet == weightAdims `HS.difference` inputAdims

    assert
      "input feature should be in the intersection of input and weight axes"
      $ featureAdimsSet
        `HS.isSubsetOf` (inputAdims `HS.intersection` weightAdims)
    let spatialAdims =
          inputAdims `HS.difference` (batchAdimsSet <> featureAdimsSet)
    assert "strides must have the same axes as spatial axes" $
      HS.fromList (HM.keys stridesMap) == spatialAdims
    checkParamsWellFormed shapeInput stridesMap
    checkParamsWellFormed shapeInput siMapsMap

    resultShapeBatch <- restrictAbstractShape shapeInput batchAdimsSet
    resultShapeOutputFeature <-
      restrictAbstractShape shapeWeights outputFeatureAdimsSet
    resultSpatialShape <- restrictAbstractShape shapeInput spatialAdims
    resultShape <-
      concatAbstractShape resultShapeBatch resultSpatialShape
        >>= concatAbstractShape resultShapeOutputFeature
    return (resultShape, tyInput)

convBaseImpl ::
  (ExprInContext input, ExprInContext weights) =>
  input ->
  weights ->
  ConvConfig ->
  DSLContext Expr
convBaseImpl
  input'
  weights'
  config@ConvConfig {..} = do
    input <- liftInContext input'
    weights <- liftInContext weights'
    let stridesMap = toParamMaps strides
        siMapsMap = toParamMaps contractingSIMaps
    internWithCheck
      ( UConvBase input weights $
          ConvConfigArgsExpr
            { batchAdims = batchAdims,
              featureAdims = featureAdims,
              outputFeatureAdims = outputFeatureAdims,
              strides = stridesMap,
              contractingSIMaps = siMapsMap
            }
      )
      $ do
        inputShapeTy <- shapeAndTypeOf input
        weightsShapeTy <- shapeAndTypeOf weights
        convBaseCheck inputShapeTy weightsShapeTy config

convImpl ::
  (ExprInContext input, ExprInContext weights) =>
  input ->
  weights ->
  ConvConfig ->
  ConvPadding ->
  DSLContext Expr
convImpl
  input'
  weights'
  config@ConvConfig {..}
  ConvPadding {..} = do
    input <- liftInContext input'
    weights <- liftInContext weights'
    let stridesMap = toParamMaps strides
        siMapsMap = toParamMaps contractingSIMaps
        padl = toParamMaps low
        padldilation = toParamMaps ldilation
        padh = toParamMaps high
        padrdilation = toParamMaps rdilation
    internWithCheck
      ( UConv
          input
          weights
          ConvConfigArgsExpr
            { batchAdims = batchAdims,
              featureAdims = featureAdims,
              outputFeatureAdims = outputFeatureAdims,
              strides = stridesMap,
              contractingSIMaps = siMapsMap
            }
          ConvPaddingArgsExpr
            { low = padl,
              ldilation = padldilation,
              high = padh,
              rdilation = padrdilation
            }
      )
      $ do
        inputShapeTy@(_, dtype) <- shapeAndTypeOf input
        padElem <- case dtype of
          IntType -> return $ toElem (0 :: TensorInt)
          RealType -> return $ toElem (0 :: TensorReal)
          BoolType -> mrgThrowError "Cannot conv a boolean tensor"
        -- Only check adims
        inputPaddedShapeTy <-
          padCheck inputShapeTy padElem $
            Padding {low = low, interior = ldilation, high = high}
        weightsShapeTy <- shapeAndTypeOf weights
        weightsPaddedShapeTy <-
          padCheck weightsShapeTy padElem $
            Padding {low = [], interior = rdilation, high = []}
        convBaseCheck
          inputPaddedShapeTy
          weightsPaddedShapeTy
          config

-- | Clamp operator.
clamp ::
  (ExprInContext e, ExprInContext emin, ExprInContext emax) =>
  -- | The minimum value.
  emin ->
  -- | The tensor to clamp.
  e ->
  -- | The maximum value.
  emax ->
  DSLContext Expr
clamp emin' e' emax' = do
  emin <- liftInContext emin'
  e <- liftInContext e'
  emax <- liftInContext emax'
  internWithCheck (UClamp emin e emax) $ do
    (eminShape, eminType) <- shapeAndTypeOf emin
    (eShape, eType) <- shapeAndTypeOf e
    (emaxShape, emaxType) <- shapeAndTypeOf emax
    assert "shape of emin must equal to shape of e" $ eminShape == eShape
    assert "shape of emax must equal to shape of e" $ emaxShape == eShape
    assert "type of emin must be int or real" $ eminType `elem` [IntType, RealType]
    assert "type of emax must be the same as emin" $ emaxType == eminType
    assert "type of e must be the same as emin" $ eType == eminType
    return (eShape, eminType)

-- | Clamp scalar operator.
clampScalar ::
  (ToElem a, ToDType a, ExprInContext e) =>
  -- | The minimum value.
  a ->
  -- | The tensor to clamp.
  e ->
  -- | The maximum value.
  a ->
  DSLContext Expr
clampScalar imin e' imax = do
  e <- liftInContext e'
  internWithCheck (UClampScalar (toElem imin) e (toElem imax)) $ do
    (eShape, eType) <- shapeAndTypeOf e
    let iminType = toDType imin
    let imaxType = toDType imax
    assert "type of e must be int or real" $ eType `elem` [IntType, RealType]
    assert "type of imin must be the same as e" $ iminType == eType
    assert "type of imax must be the same as e" $ imaxType == eType
    return (eShape, eType)

-- | Select operation.
select ::
  (ExprInContext c, ExprInContext t, ExprInContext e) =>
  -- | The condition tensor.
  c ->
  -- | The tensor to take on true.
  t ->
  -- | The tensor to take on false.
  e ->
  DSLContext Expr
select c' t' e' = do
  c <- liftInContext c'
  t <- liftInContext t'
  e <- liftInContext e'
  internWithCheck (USelect c t e) $ do
    (cShape, cType) <- shapeAndTypeOf c
    (tShape, tType) <- shapeAndTypeOf t
    (eShape, eType) <- shapeAndTypeOf e
    assert "shape of c must equal to shape of t" $ cShape == tShape
    assert "shape of c must equal to shape of e" $ cShape == eShape
    assert "type of c must be bool" $ cType == BoolType
    assert "type of t must equal to type of e" $ tType == eType
    return (tShape, tType)

reshapeDegenerate ::
  (ExprInContext e) =>
  e ->
  [(AdimRef, AdimIdentifier)] ->
  [AdimRef] ->
  DSLContext Expr
reshapeDegenerate e' introAdims elimAdims = do
  e <- liftInContext e'
  internWithCheck (UReshapeDegenerate e introAdims elimAdims) $ do
    shape <- shapeOf e
    ty <- typeOf e
    let allRefs = abstractShapeAllRefs shape
    assert "elimAdims must be a subset of all axes" $
      HS.fromList elimAdims `HS.isSubsetOf` allRefs
    assert "introAdims must not overlap with the set of all axes" $
      HS.null $
        HS.fromList (fst <$> introAdims) `HS.intersection` allRefs
    newShape0 <-
      foldM
        (uncurry . addAdimByAdimRef)
        shape
        introAdims
    newShape <- foldM removeAdim newShape0 elimAdims
    return (newShape, ty)

-- | Reverse operation.
reverseTensor ::
  (ExprInContext e) =>
  -- | The tensor to reverse.
  e ->
  -- | The axes to reverse on.
  [AdimRef] ->
  DSLContext Expr
reverseTensor e' adims = do
  e <- liftInContext e'
  internWithCheck (UReverseTensor e adims) $ do
    shape <- shapeOf e
    ty <- typeOf e
    let allRefs = abstractShapeAllRefs shape
    assert "adims must be a subset of all axes" $
      HS.fromList adims `HS.isSubsetOf` allRefs
    return (shape, ty)

type ValidElem a = (IsString a, ToElem a, ToDType a)

type family BaseNum x where
  BaseNum (TensorNum a) = a

type ValidNum a =
  ( ValidElem a,
    Num a,
    Mergeable (BaseNum a),
    a ~ TensorNum (BaseNum a)
  )

type AnyDTypeRule a =
  forall p. (ValidElem a) => p a -> DSLContext Rewrite

type NumRule a =
  forall p. (ValidNum a) => p a -> DSLContext Rewrite

checkSIMap :: [MapIdentifier] -> [MapIdentifier] -> DSLContext ()
checkSIMap lhs rhs = do
  let lhsSet = HS.fromList lhs
      rhsSet = HS.fromList rhs
  assert "lhs and rhs must not have the same si-maps" $
    HS.null $
      HS.intersection lhsSet rhsSet
  modify $ \env ->
    env
      { lhsSIMaps = HS.union lhsSet $ lhsSIMaps env,
        rhsSIMaps = HS.union rhsSet $ rhsSIMaps env
      }
