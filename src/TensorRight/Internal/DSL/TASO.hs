{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}

module TensorRight.Internal.DSL.TASO
  ( enlarge,
  )
where

import Grisette (SymInteger)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import TensorRight.Internal.Core.Tensor (DType (IntType, RealType))
import TensorRight.Internal.DSL.DSL
  ( DSLContext,
    Expr,
    ExprInContext,
    liftInContext,
    shapeOf,
    typeOf,
  )
import TensorRight.Internal.DSL.Expr
  ( UExpr (UEnlarge),
    checkParamsWellFormed,
    internWithCheck,
  )
import TensorRight.Internal.DSL.Identifier (MapIdentifier)
import TensorRight.Internal.DSL.Parameters (IsParamMaps (toParamMaps), ParamDesc (ParamDesc))
import TensorRight.Internal.DSL.Syntax (ArrowSyntax ((-->)))
import TensorRight.Internal.Util.Error (assert)

-- | TASO's enlarge operator. The backend asserts non-negative target sizes and
-- the deterministic floor split of the additional padding.
enlarge ::
  (ExprInContext e) =>
  ParamDesc ->
  ParamDesc ->
  MapIdentifier ->
  MapIdentifier ->
  SymInteger ->
  SymInteger ->
  e ->
  DSLContext Expr
enlarge h@(ParamDesc hRef _) w@(ParamDesc wRef _) hLow wLow ky kx e' = do
  e <- liftInContext e'
  let targetSizes = [(hRef, ky), (wRef, kx)]
      targetMaps = toParamMaps [h, w]
      lowPadding = toParamMaps ([hRef --> hLow, wRef --> wLow] :: [ParamDesc])
  internWithCheck (UEnlarge e targetSizes lowPadding) $ do
    shape <- shapeOf e
    dtype <- typeOf e
    assert "enlarge: tensor must have integer or real type" $
      dtype `elem` [IntType, RealType]
    assert "enlarge: lower-padding rclasses must equal target-size rclasses" $
      HM.keysSet lowPadding == HS.fromList (fst <$> targetSizes)
    checkParamsWellFormed shape targetMaps
    checkParamsWellFormed shape lowPadding
    return (shape, dtype)
