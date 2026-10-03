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
    liftInContext,
    numBinOp,
    numBinScalarOp,
    rankPrecondition,
    shapeOf,
    typeOf,
  )
import Control.Monad.Except (MonadError (throwError))
import qualified TensorRight.Internal.DSL.Expr as E
import TensorRight.Internal.DSL.Expr
  ( UExpr (UEnlarge),
    internWithCheck,
  )
import TensorRight.Internal.DSL.Shape
  ( RClassRef,
    abstractShapeAllRefs,
    getRClassByRClassRef,
  )
import TensorRight.Internal.Util.Error (assert)
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
