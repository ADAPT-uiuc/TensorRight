{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveLift #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TensorRight.Internal.DSL.Eval
  ( getAxisName,
    getAxisMapLike,
    SymIdentInfo (..),
    evalRewrite,
    eval,
    EvalState (..),
    freshMapBase,
    modifyMaps,
  )
where

import Control.Arrow (Arrow (first))
import Control.DeepSeq (NFData)
import Control.Monad.State (MonadState (get), State, gets, modify')
import Data.Foldable (Foldable (toList))
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Hashable (Hashable)
import qualified Data.Set.Ordered as OS
import qualified Data.Text as T
import GHC.Generics (Generic)
import Grisette
  ( AsMetadata (asMetadata, fromMetadata),
    LogicalOp (false, (.||)),
    SExpr (Atom, List),
    SymBool,
    SymEq ((./=)),
    SymInteger (SymInteger),
    TypedSymbol (TypedSymbol),
    mapIdentifier,
    mapMetadata,
    withMetadata,
    pattern SymTerm,
  )
import Language.Haskell.TH.Syntax (Lift)
import TensorRight.Internal.Core.Axis
  ( Axes,
    Axis (Axis, LabelledAxis),
    AxisMapLike (fromHashMap),
    Indices,
    Sizes,
  )
import TensorRight.Internal.Core.Tensor
  ( DType,
    Elem (BoolElem),
    Tensor,
    boolBinOp,
    boolScalarBinOp,
    boolUnaryOp,
    broadcast,
    clamp,
    clampScalar,
    compareOp,
    concatTensor,
    concatTensorList,
    constantTensor,
    conv,
    convBase,
    createTensor,
    dot,
    dynamicSlice,
    dynamicUpdateSlice,
    iota,
    numBinOp,
    numScalarBinOp,
    numUnaryOp,
    pad,
    padLow,
    reduce,
    relabel,
    reshapeDegenerate,
    reverseTensor,
    select,
    slice,
  )
import TensorRight.Internal.Core.Tensor.Typed
  ( ConvConfigArgs
      ( ConvConfigArgs,
        convBatchAxes,
        convContractingSIMap,
        convFeatureAxes,
        convOutputFeatureAxes,
        convStrides
      ),
    ConvPaddingArgs
      ( ConvPaddingArgs,
        convHighPadding,
        convLDilation,
        convLowPadding,
        convRDilation
      ),
    DySliceArgs (DySliceArgs, sizes, start),
    PaddingArgs (PaddingArgs, highPad, interiorPad, lowPad),
    SliceArgs (SliceArgs, end, start, strides),
    TensorElem (TensorElemVal),
  )
import TensorRight.Internal.DSL.Expr
  ( ConvConfigArgsExpr
      ( ConvConfigArgsExpr,
        batchRClasses,
        contractingSIMaps,
        featureRClasses,
        outputFeatureRClasses,
        strides
      ),
    ConvPaddingArgsExpr (ConvPaddingArgsExpr, high, ldilation, low, rdilation),
    DySliceArgsExpr (DySliceArgsExpr, sizes, start),
    Expr
      ( BoolBinOp,
        BoolScalarBinOp,
        BoolUnaryOp,
        Broadcast,
        Clamp,
        ClampScalar,
        CompareOp,
        Concat,
        ConcatList,
        Constant,
        Conv,
        ConvBase,
        Dot,
        DynamicSlice,
        DynamicUpdateSlice,
        Iota,
        NumBinOp,
        NumScalarBinOp,
        NumUnaryOp,
        Pad,
        PadLow,
        Reduce,
        Relabel,
        ReshapeDegenerate,
        ReverseTensor,
        Select,
        Slice,
        Var
      ),
    PaddingArgsExpr (PaddingArgsExpr, high, interior, low),
    Params,
    Rewrite (Rewrite),
    SliceArgsExpr (SliceArgsExpr, end, start, strides),
    exprId,
  )
import TensorRight.Internal.DSL.Identifier (MapIdentifier, RClassIdentifier, TensorIdentifier)
import TensorRight.Internal.DSL.Shape
  ( AbstractShape (AbstractShape),
    RClassRef (ByLabel, ByRClass),
    TensorShape (labelled, unlabelled),
    toAbstractShape,
  )
import TensorRight.Internal.Util.Error (ErrorEnv)

type MapBase = HM.HashMap T.Text SymInteger

freshMapBase :: String -> MapBase -> (SymBool, MapBase)
freshMapBase name mapBase =
  ( HM.foldlWithKey
      (\acc k v -> acc .|| (new HM.! k ./= v))
      false
      mapBase,
    new
  )
  where
    new =
      HM.map
        ( \(SymInteger (SymTerm (TypedSymbol s :: TypedSymbol knd a))) ->
            SymInteger $
              SymTerm
                ( TypedSymbol $
                    mapIdentifier
                      (mapMetadata (\m -> List [Atom "fresh", Atom $ T.pack name, m]))
                      s ::
                    TypedSymbol knd a
                )
        )
        mapBase

modifyMaps ::
  String ->
  HS.HashSet MapIdentifier ->
  HM.HashMap MapIdentifier MapBase ->
  (SymBool, HM.HashMap MapIdentifier MapBase)
modifyMaps name maps allMaps =
  ( HM.foldlWithKey
      ( \acc mapIdent mapBase ->
          if HS.member mapIdent maps
            then acc .|| fst (freshMapBase name mapBase)
            else acc
      )
      false
      allMaps,
    new
  )
  where
    new = flip HM.mapWithKey allMaps $ \mapIdent mapBase ->
      if HS.member mapIdent maps
        then snd $ freshMapBase name mapBase
        else mapBase

data EvalState = EvalState
  { rclasses :: HM.HashMap RClassIdentifier (OS.OSet Int),
    maps :: HM.HashMap MapIdentifier MapBase,
    allTensorShapes :: HM.HashMap TensorIdentifier TensorShape,
    allTensorDTypes :: HM.HashMap TensorIdentifier DType,
    evaluated :: HM.HashMap Int (ErrorEnv Tensor),
    exprShapes :: HM.HashMap Int AbstractShape
  }
  deriving (Show, Generic)

type EvalContext = State EvalState

getAxisMapLike :: (AxisMapLike m) => RClassRef -> MapIdentifier -> EvalContext m
getAxisMapLike ref map = do
  maps <- gets maps
  case HM.lookup map maps of
    Just m -> case ref of
      ByRClass _ -> return $ fromHashMap $ HM.mapKeys Axis m
      ByLabel label -> return $ fromHashMap $ HM.mapKeys (LabelledAxis label) m
    Nothing -> error $ "Map " <> show map <> "not found"

getRClassByRClassRef :: AbstractShape -> RClassRef -> EvalContext RClassIdentifier
getRClassByRClassRef (AbstractShape _ u) (ByRClass rclass) = do
  if HS.member rclass u
    then return rclass
    else error $ "RClass " <> show rclass <> " not found in shape"
getRClassByRClassRef (AbstractShape l _) (ByLabel label) = do
  case HM.lookup label l of
    Nothing -> error $ "Label " <> show label <> " not found in shape"
    Just rclass -> return rclass

getAxisName :: RClassIdentifier -> Int -> T.Text
getAxisName rclass i = T.pack $ show rclass <> "." <> show i

getAxesList :: RClassRef -> RClassIdentifier -> EvalContext [Axis]
getAxesList (ByRClass rclass) _ = do
  rclasses <- gets rclasses
  case HM.lookup rclass rclasses of
    Nothing -> error $ "RClass " <> show rclass <> " not found"
    Just axes ->
      return $ Axis . getAxisName rclass <$> toList axes
getAxesList (ByLabel label) rclass = do
  rclasses <- gets rclasses
  case HM.lookup rclass rclasses of
    Nothing -> error $ "RClass " <> show rclass <> " not found"
    Just axes ->
      return $ LabelledAxis label . getAxisName rclass <$> toList axes

getAxes :: RClassRef -> RClassIdentifier -> EvalContext Axes
getAxes ref rclass = HS.fromList <$> getAxesList ref rclass

rclassToAxes :: AbstractShape -> RClassRef -> EvalContext Axes
rclassToAxes shape ref = do
  rclass <- getRClassByRClassRef shape ref
  getAxes ref rclass

rclassesToAxes :: AbstractShape -> [RClassRef] -> EvalContext Axes
rclassesToAxes shape = fmap mconcat . traverse (rclassToAxes shape)

getIndicesFromParams :: Params -> EvalContext Indices
getIndicesFromParams params = fmap mconcat $ traverse (uncurry getAxisMapLike) $ HM.toList params

getSizesFromParams :: Params -> EvalContext Sizes
getSizesFromParams params = fmap mconcat $ traverse (uncurry getAxisMapLike) $ HM.toList params

eval :: Expr -> EvalContext (ErrorEnv Tensor)
eval expr = do
  state <- get
  case HM.lookup (exprId expr) $ evaluated state of
    Just t -> return t
    Nothing -> do
      t <- eval' expr
      modify' $ \s -> s {evaluated = HM.insert (exprId expr) t $ evaluated s}
      return t

tensorShapeToSizes :: TensorShape -> EvalContext Sizes
tensorShapeToSizes shape =
  fmap mconcat $
    traverse (uncurry getAxisMapLike) $
      labelledList ++ unlabelledList
  where
    labelledList =
      fmap (\(label, (_, map)) -> (ByLabel label, map)) $
        HM.toList $
          labelled shape
    unlabelledList = fmap (first ByRClass) $ HM.toList $ unlabelled shape

exprShape :: Expr -> EvalContext AbstractShape
exprShape expr = do
  state <- get
  return $ exprShapes state HM.! exprId expr

data SymIdentInfo = SymTensor TensorIdentifier | SymMap RClassIdentifier Int MapIdentifier
  deriving (Eq, Ord, Hashable, Generic, Lift, NFData)

instance AsMetadata SymIdentInfo where
  asMetadata (SymTensor ident) = List [Atom "SymTensor", asMetadata ident]
  asMetadata (SymMap rclass int map) =
    List
      [ Atom "SymMap",
        asMetadata rclass,
        Atom $ T.pack $ show int,
        asMetadata map
      ]
  fromMetadata (List [Atom "SymMap", rclass, Atom int, map]) = do
    rclass' <- fromMetadata rclass
    map' <- fromMetadata map
    return $ SymMap rclass' (read $ T.unpack int) map'
  fromMetadata (List [Atom "SymTensor", ident]) = do
    ident' <- fromMetadata ident
    return $ SymTensor ident'
  fromMetadata _ = Nothing

instance Show SymIdentInfo where
  show (SymTensor ident) = show ident
  show (SymMap rclass int map) = show rclass <> "." <> show int <> "." <> show map

eval' :: Expr -> EvalContext (ErrorEnv Tensor)
eval' (Var _ ident) = do
  shape <- gets $ (HM.! ident) . allTensorShapes
  dtype <- gets $ (HM.! ident) . allTensorDTypes
  sizes <- tensorShapeToSizes shape
  return $
    createTensor
      (withMetadata "tensor" $ SymTensor ident)
      sizes
      dtype
eval' (NumBinOp _ op lhs rhs) = do
  l <- eval lhs
  r <- eval rhs
  return $ numBinOp op l r
eval' (NumScalarBinOp _ op lhs rhs) = do
  l <- eval lhs
  return $ numScalarBinOp op l rhs
eval' (NumUnaryOp _ op expr) = do
  e <- eval expr
  return $ numUnaryOp op e
eval' (BoolBinOp _ op lhs rhs) = do
  l <- eval lhs
  r <- eval rhs
  return $ boolBinOp op l r
eval' (BoolScalarBinOp _ op lhs rhs) = do
  l <- eval lhs
  return $ boolScalarBinOp op l $ BoolElem $ TensorElemVal rhs
eval' (BoolUnaryOp _ op expr) = do
  e <- eval expr
  return $ boolUnaryOp op e
eval' (CompareOp _ op lhs rhs) = do
  l <- eval lhs
  r <- eval rhs
  return $ compareOp op l r
eval' (Reduce _ expr abstractSI) = do
  e <- eval expr
  si <- getIndicesFromParams abstractSI
  return $ reduce e si
eval' (Broadcast _ expr extendedShape) = do
  e <- eval expr
  sizes <- tensorShapeToSizes extendedShape
  return $ broadcast e sizes
eval' (Constant _ elem shape) = do
  sizes <- tensorShapeToSizes shape
  return $ constantTensor elem sizes
eval' (Iota _ shape ref) = do
  sizes <- tensorShapeToSizes shape
  rclass <- getRClassByRClassRef (toAbstractShape shape) ref
  axes <- getAxes ref rclass
  if HS.size axes /= 1
    then error "Iota: rclass must have a single axis"
    else return $ iota sizes (head $ HS.toList axes)
eval' (Slice _ expr SliceArgsExpr {..}) = do
  e <- eval expr
  start <- getIndicesFromParams start
  end <- getIndicesFromParams end
  strides <- getIndicesFromParams strides
  return $ slice e $ SliceArgs {..}
eval' (Pad _ expr elem PaddingArgsExpr {..}) = do
  e <- eval expr
  l <- getSizesFromParams low
  h <- getSizesFromParams high
  i <- getSizesFromParams interior
  return $ pad e elem $ PaddingArgs {lowPad = l, interiorPad = i, highPad = h}
eval' (PadLow _ expr elem lowPadding) = do
  e <- eval expr
  l <- getSizesFromParams lowPadding
  return $ padLow e elem l
eval' (DynamicSlice _ expr DySliceArgsExpr {..}) = do
  e <- eval expr
  start <- getIndicesFromParams start
  sizes <- getSizesFromParams sizes
  return $ dynamicSlice e $ DySliceArgs {..}
eval' (DynamicUpdateSlice _ expr update start) = do
  e <- eval expr
  u <- eval update
  s <- getIndicesFromParams start
  return $ dynamicUpdateSlice e u s
eval' (Concat _ lhs rhs ref) = do
  l <- eval lhs
  r <- eval rhs
  lShape <- gets $ (HM.! exprId lhs) . exprShapes
  rclass <- getRClassByRClassRef lShape ref
  axes <- getAxes ref rclass
  if HS.size axes /= 1
    then error "Concat: rclass must have a single axis"
    else return $ concatTensor l r (head $ HS.toList axes)
eval' (ConcatList _ exprs ref) = do
  es <- traverse eval exprs
  headShape <- gets $ (HM.! exprId (head exprs)) . exprShapes
  rclass <- getRClassByRClassRef headShape ref
  axes <- getAxes ref rclass
  if HS.size axes /= 1
    then error "ConcatList: rclass must have a single axis"
    else return $ concatTensorList es (head $ HS.toList axes)
eval' (Relabel _ expr map) = do
  e <- eval expr
  originalShape <- exprShape expr
  loweredRelabelMap <-
    mconcat
      <$> mapM (uncurry $ mapEntryToAxesMap originalShape) (HM.toList map)
  return $ relabel e loweredRelabelMap
  where
    mapEntryToAxesMap originalShape from to = do
      fromRClass <- getRClassByRClassRef originalShape from
      fromAxesList <- getAxesList from fromRClass
      toAxesList <- getAxesList to fromRClass
      return $ HM.fromList $ zip fromAxesList toAxesList
eval' (Dot _ lhs rhs contractingSIMaps batch) = do
  l <- eval lhs
  r <- eval rhs
  lhsShape <- exprShape lhs
  contractingSI <- getIndicesFromParams contractingSIMaps
  batchAxes <- rclassesToAxes lhsShape batch
  return $ dot l r contractingSI batchAxes
eval'
  ( ConvBase
      _
      input
      weight
      ConvConfigArgsExpr {..}
    ) = do
    i <- eval input
    w <- eval weight
    lhsShape <- exprShape input
    rhsShape <- exprShape weight
    batchAxes <- rclassesToAxes lhsShape batchRClasses
    featureAxes <- rclassesToAxes lhsShape featureRClasses
    outputFeatureAxes <- rclassesToAxes rhsShape outputFeatureRClasses
    s <- getIndicesFromParams strides
    si <- getIndicesFromParams contractingSIMaps
    return $
      convBase i w $
        ConvConfigArgs
          { convBatchAxes = batchAxes,
            convFeatureAxes = featureAxes,
            convOutputFeatureAxes = outputFeatureAxes,
            convStrides = s,
            convContractingSIMap = si
          }
eval'
  ( Conv
      _
      input
      weight
      ConvConfigArgsExpr {..}
      ConvPaddingArgsExpr {..}
    ) = do
    i <- eval input
    w <- eval weight
    lhsShape <- exprShape input
    rhsShape <- exprShape weight
    batchAxes <- rclassesToAxes lhsShape batchRClasses
    featureAxes <- rclassesToAxes lhsShape featureRClasses
    outputFeatureAxes <- rclassesToAxes rhsShape outputFeatureRClasses
    s <- getIndicesFromParams strides
    si <- getIndicesFromParams contractingSIMaps
    l <- getSizesFromParams low
    ld <- getSizesFromParams ldilation
    h <- getSizesFromParams high
    rd <- getSizesFromParams rdilation
    return $
      conv
        i
        w
        ConvConfigArgs
          { convBatchAxes = batchAxes,
            convFeatureAxes = featureAxes,
            convOutputFeatureAxes = outputFeatureAxes,
            convStrides = s,
            convContractingSIMap = si
          }
        ConvPaddingArgs
          { convLowPadding = l,
            convLDilation = ld,
            convHighPadding = h,
            convRDilation = rd
          }
eval' (Clamp _ emin' e' emax') = do
  emin <- eval emin'
  e <- eval e'
  emax <- eval emax'
  return $ clamp emin e emax
eval' (ClampScalar _ imin' e' imax') = do
  e <- eval e'
  return $ clampScalar imin' e imax'
eval' (Select _ c' t' e') = do
  c <- eval c'
  t <- eval t'
  e <- eval e'
  return $ select c t e
eval' (ReverseTensor _ expr axes) = do
  shape <- exprShape expr
  reverseAxes <- rclassesToAxes shape axes
  e <- eval expr
  return $ reverseTensor e reverseAxes
eval' res@(ReshapeDegenerate _ expr introAxes elimAxes) = do
  e <- eval expr
  shape <- exprShape expr
  resShape <- exprShape res
  introAxes' <- rclassesToAxes resShape (fst <$> introAxes)
  elimAxes' <- rclassesToAxes shape elimAxes
  return $ reshapeDegenerate e introAxes' elimAxes'

evalRewrite :: Rewrite -> EvalContext (ErrorEnv Tensor, ErrorEnv Tensor)
evalRewrite (Rewrite _ lhs rhs) = do
  l <- eval lhs
  r <- eval rhs
  return (l, r)
