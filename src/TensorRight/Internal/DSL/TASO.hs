{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module TensorRight.Internal.DSL.TASO
  ( enlarge,
  )
where

import qualified Data.HashSet as HS
import Data.Foldable (traverse_)
import TensorRight.Internal.Core.Tensor (DType (IntType, RealType))
import TensorRight.Internal.DSL.DSL
  ( DSLContext,
    Expr,
    ExprInContext,
    liftInContext,
    rankPrecondition,
    shapeOf,
    typeOf,
  )
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
