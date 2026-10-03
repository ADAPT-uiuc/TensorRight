{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module TensorRight.Internal.DSL.TASO
  ( ewadd,
    ewmul,
    smul,
    relu,
    concat,
    split0,
    split1,
    transpose,
    matmul2D,
    TasoPaddingMode (..),
    Activation (..),
    tasoConv,
    enlarge,
  )
where

import qualified Data.HashSet as HS
import Data.Foldable (traverse_)
import TensorRight.Internal.Core.Tensor
  ( DType (IntType, RealType),
    ToDType,
    ToElem,
  )
import TensorRight.Internal.Core.Tensor.TensorInt (posInf)
import TensorRight.Internal.DSL.DSL
  ( NumBinOp (Add, Mul),
    DSLContext,
    Expr,
    ExprInContext,
    ValidNum,
    clampScalar,
    concatTensor,
    ConvConfig (..),
    ConvPadding (..),
    dot,
    liftInContext,
    newMap,
    numBinOp,
    numBinScalarOp,
    rankPrecondition,
    relabel,
    shapeOf,
    tasoConvImpl,
    typeOf,
  )
import Control.Monad.Except (MonadError (throwError))
import qualified TensorRight.Internal.DSL.Expr as E
import TensorRight.Internal.DSL.Expr
  ( TasoPaddingMode (..),
    UExpr (UEnlarge),
    internWithCheck,
  )
import TensorRight.Internal.DSL.Shape
  ( RClassRef,
    abstractShapeAllRefs,
    getRClassByRClassRef,
  )
import TensorRight.Internal.DSL.Parameters (ParamDesc (ParamDesc))
import TensorRight.Internal.Util.Error (assert)
import TensorRight.Internal.DSL.Syntax (ArrowSyntax ((-->)))
import Prelude hiding (concat)

-- | TASO's elementwise addition has exactly TensorRight's numeric
-- elementwise-addition semantics.
ewadd :: (ExprInContext lhs, ExprInContext rhs) => lhs -> rhs -> DSLContext Expr
ewadd = numBinOp Add

-- | TASO's elementwise multiplication has exactly TensorRight's numeric
-- elementwise-multiplication semantics.
ewmul :: (ExprInContext lhs, ExprInContext rhs) => lhs -> rhs -> DSLContext Expr
ewmul = numBinOp Mul

-- | TASO's scalar multiplication has exactly TensorRight's numeric
-- tensor/scalar-multiplication semantics.
smul :: (ExprInContext lhs, ToElem a, ToDType a) => lhs -> a -> DSLContext Expr
smul = numBinScalarOp Mul

-- | TASO's ReLU is a clamp from zero to positive infinity.
relu :: forall a lhs. (ExprInContext lhs, ValidNum a) => lhs -> DSLContext Expr
relu e = clampScalar @a 0 e posInf

-- | TASO's concat has exactly TensorRight's concatenation semantics. The
-- selected rclass is fixed to rank one by 'concatTensor', so it denotes one
-- concrete TASO axis.
concat ::
  (ExprInContext lhs, ExprInContext rhs) =>
  RClassRef ->
  lhs ->
  rhs ->
  DSLContext Expr
concat axis lhs rhs = concatTensor lhs rhs axis

-- | The first output of TASO's paper-level split operator. This deliberately
-- models only the split--concat axiom: its input must be a concat on @axis@,
-- and it returns that concat's left operand. General split-tree provenance is
-- outside the scope of this operator.
split0 :: (ExprInContext e) => RClassRef -> e -> DSLContext Expr
split0 axis expr' = do
  expr <- liftInContext expr'
  case expr of
    E.Concat _ lhs _ concatAxis
      | concatAxis == axis -> return lhs
      | otherwise -> throwError "TASO split0: concat axis does not match split axis"
    _ -> throwError "TASO split0: input must be a concat"

-- | The second output of TASO's paper-level split operator. See 'split0' for
-- the intentional direct-concat restriction.
split1 :: (ExprInContext e) => RClassRef -> e -> DSLContext Expr
split1 axis expr' = do
  expr <- liftInContext expr'
  case expr of
    E.Concat _ _ rhs concatAxis
      | concatAxis == axis -> return rhs
      | otherwise -> throwError "TASO split1: concat axis does not match split axis"
    _ -> throwError "TASO split1: input must be a concat"

-- | TASO's rule-level transpose. Although TASO's graph API also exposes
-- arbitrary-rank permutations, its published rewrite axioms use only the
-- matrix transpose: a rank-two swap. Each abstract axis is therefore fixed
-- to one concrete axis before desugaring to TensorRight's general relabel.
transpose :: (ExprInContext e) => e -> DSLContext Expr
transpose expr' = do
  expr <- liftInContext expr'
  shape <- shapeOf expr
  let refs = HS.toList $ abstractShapeAllRefs shape
  assert "tasoTranspose: input must have exactly two axes" $ length refs == 2
  rclasses <- traverse (getRClassByRClassRef shape) refs
  traverse_ (`rankPrecondition` 1) rclasses
  let [first, second] = refs
  relabel expr [first --> second, second --> first]

-- | TASO's rule-level matrix multiplication. TASO's graph implementation can
-- construct batched matmuls, but its published axiom set restricts matmul to
-- two-dimensional matrices. The sole entry in @contract@ selects the shared
-- inner dimension.
matmul2D ::
  (ExprInContext lhs, ExprInContext rhs) =>
  lhs ->
  rhs ->
  [ParamDesc] ->
  DSLContext Expr
matmul2D lhs' rhs' contract = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  lhsShape <- shapeOf lhs
  rhsShape <- shapeOf rhs
  let lhsRefs = HS.toList $ abstractShapeAllRefs lhsShape
      rhsRefs = HS.toList $ abstractShapeAllRefs rhsShape
  assert "tasoMatmul2D: left input must have exactly two axes" $ length lhsRefs == 2
  assert "tasoMatmul2D: right input must have exactly two axes" $ length rhsRefs == 2
  assert "tasoMatmul2D: expected exactly one contracting axis" $ length contract == 1
  lhsRClasses <- traverse (getRClassByRClassRef lhsShape) lhsRefs
  rhsRClasses <- traverse (getRClassByRClassRef rhsShape) rhsRefs
  traverse_ (`rankPrecondition` 1) $ lhsRClasses <> rhsRClasses
  dot lhs rhs contract []

-- | Activations accepted by TASO's Conv2D operator.
data Activation = None | Relu
  deriving (Eq, Show)

-- | TASO's rank-four Conv2D. The frontend establishes only the structural
-- operator contract. The backend asserts the @SAME@/@VALID@ padding equations
-- and unit-dilation restriction before evaluating the existing convolution.
tasoConv ::
  forall a input weights.
  (ExprInContext input, ExprInContext weights, ValidNum a) =>
  ConvConfig ->
  TasoPaddingMode ->
  Activation ->
  input ->
  weights ->
  DSLContext Expr
tasoConv config mode activation input' weights' = do
  input <- liftInContext input'
  weights <- liftInContext weights'
  inputShape <- shapeOf input
  weightShape <- shapeOf weights
  let inputRefs = HS.toList $ abstractShapeAllRefs inputShape
      weightRefs = HS.toList $ abstractShapeAllRefs weightShape
      spatialRefs = [ref | ParamDesc ref _ <- strides config]
  assert "tasoConv: input must have exactly four axes" $ length inputRefs == 4
  assert "tasoConv: weights must have exactly four axes" $ length weightRefs == 4
  assert "tasoConv: expected one batch rclass" $ length (batchRClasses config) == 1
  assert "tasoConv: expected one input-feature rclass" $ length (featureRClasses config) == 1
  assert "tasoConv: expected one output-feature rclass" $ length (outputFeatureRClasses config) == 1
  assert "tasoConv: expected two spatial stride rclasses" $ length spatialRefs == 2
  inputRClasses <- traverse (getRClassByRClassRef inputShape) inputRefs
  weightRClasses <- traverse (getRClassByRClassRef weightShape) weightRefs
  traverse_ (`rankPrecondition` 1) $ inputRClasses <> weightRClasses
  let freshPadding name =
        traverse
          (\ref -> ParamDesc ref <$> (newMap name =<< getRClassByRClassRef inputShape ref))
          spatialRefs
  low <- freshPadding "tasoConvLow"
  ldilation <- freshPadding "tasoConvLDilation"
  high <- freshPadding "tasoConvHigh"
  rdilation <- freshPadding "tasoConvRDilation"
  output <-
    tasoConvImpl input weights mode config $
      ConvPadding
        { low = low,
          ldilation = ldilation,
          high = high,
          rdilation = rdilation
        }
  case activation of
    None -> return output
    Relu -> relu @a output

-- | TASO's rank-four enlarge operator. It centers @source@ in the H/W shape
-- of @reference@. The frontend fixes the four abstract axes to singleton
-- rclasses; Core asserts the resulting concrete rank and size constraints.
enlarge ::
  (ExprInContext source, ExprInContext reference) =>
  RClassRef ->
  RClassRef ->
  source ->
  reference ->
  DSLContext Expr
enlarge h w source' reference' = do
  source <- liftInContext source'
  reference <- liftInContext reference'
  internWithCheck (UEnlarge source reference [h, w]) $ do
    sourceShape <- shapeOf source
    referenceShape <- shapeOf reference
    sourceType <- typeOf source
    referenceType <- typeOf reference
    assert "tasoEnlarge: source must have integer or real type" $
      sourceType `elem` [IntType, RealType]
    assert "tasoEnlarge: source and reference must have the same axes" $
      sourceShape == referenceShape
    assert "tasoEnlarge: source and reference must have the same type" $
      sourceType == referenceType
    let sourceRefs = abstractShapeAllRefs sourceShape
    assert "tasoEnlarge: source must have exactly four axes" $
      HS.size sourceRefs == 4
    sourceRClasses <- traverse (getRClassByRClassRef sourceShape) $ HS.toList sourceRefs
    traverse_ (`rankPrecondition` 1) sourceRClasses
    assert "tasoEnlarge: spatial axes must be distinct source axes" $
      HS.fromList [h, w] `HS.isSubsetOf` sourceRefs
        && h /= w
    return (sourceShape, sourceType)
