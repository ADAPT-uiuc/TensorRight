{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-missing-import-lists #-}

module TensorRight.Internal.DSL.TASO
  ( ewadd,
    ewmul,
    smul,
    relu,
    concat,
    transpose,
    enlarge,
    matmul2D,
  )
where

import Grisette (SymInteger, symIte, (.&&), (.<=), (.==), (.>=))
import TensorRight (NumBinOp (Add, Mul), ToElem, concatTensor, posInf)
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL
  ( DSLContext,
    Expr,
    ExprInContext,
    Padding (..),
    RClassRef,
    ValidNum,
    clampScalar,
    combineMap,
    matmul2DHelper,
    newConstMap,
    newNonNegMap,
    numBinOp,
    numBinScalarOp,
    pad,
    precondition,
    transpose2D,
  )
import TensorRight.Internal.DSL.Expr (getRClassByMap)
import TensorRight.Internal.DSL.Identifier (MapIdentifier)
import TensorRight.Internal.DSL.Parameters (ParamDesc (..))
import TensorRight.Internal.DSL.Syntax (ArrowSyntax ((-->)))
import Prelude hiding (concat)

-- | TASO's ewadd operator. The lhs and rhs must have the same shape and the type must be either 'IntType' or 'RealType'.
ewadd ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | Lhs expression.
  lhs ->
  -- | Rhs expression.
  rhs ->
  DSLContext Expr
ewadd = numBinOp Add

-- | TASO's ewmul operator. The lhs and rhs must have the same shape and the type must be either 'IntType' or 'RealType'.
ewmul ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | Lhs expression.
  lhs ->
  -- | Rhs expression.
  rhs ->
  DSLContext Expr
ewmul = numBinOp Mul

-- | TASO's smul operator. The dtype of lhs must be 'IntType' or 'RealType'.
smul ::
  (ExprInContext lhs, ToElem a, ToDType a) =>
  -- | Lhs expression.
  lhs ->
  -- | Rhs scalar.
  a ->
  DSLContext Expr
smul = numBinScalarOp Mul

-- | TASO's relu operator
relu ::
  forall a lhs.
  (ExprInContext lhs, ValidNum a) =>
  -- | The tensor to clamp
  lhs ->
  DSLContext Expr
relu e = clampScalar @a 0 e posInf

-- | TASO's concat operator
concat ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The aggregated-axis to concat on.
  RClassRef ->
  -- | The left-hand side tensor.
  lhs ->
  -- | The right-hand side tensor.
  rhs ->
  DSLContext Expr
concat axis lhs' rhs' = concatTensor lhs' rhs' axis

-- | TASO's transpose operator
transpose ::
  (ExprInContext e) =>
  -- | The tensor to transpose
  e ->
  DSLContext Expr
transpose = transpose2D

-- | TASO's enlarge operator
enlarge ::
  forall a e.
  (ExprInContext e, ValidNum a) =>
  -- | Size descriptor for H axis: provides the axis ref and the existing size map of A along H.
  ParamDesc ->
  -- | Size descriptor for W axis: provides the axis ref and the existing size map of A along W.
  ParamDesc ->
  -- | Target size ky for H (abstract scalar).
  SymInteger ->
  -- | Target size kx for W (abstract scalar).
  SymInteger ->
  -- | The tensor to enlarge.
  e ->
  DSLContext Expr
enlarge (ParamDesc hRef sH) (ParamDesc wRef sW) ky kx e = do
  -- Promote scalars kx, ky to constant maps on the corresponding rclasses
  rH <- getRClassByMap sH
  rW <- getRClassByMap sW
  kH <- newConstMap "kH" ky rH
  kW <- newConstMap "kW" kx rW

  -- Target sizes via max
  sH' <- combineMap "sH'" (\[a, k] -> symIte (a .>= k) a k) [sH, kH]
  sW' <- combineMap "sW'" (\[a, k] -> symIte (a .>= k) a k) [sW, kW]

  -- Differences to pad
  dH <- combineMap "dH" (\[m, a] -> m - a) [sH', sH]
  dW <- combineMap "dW" (\[m, a] -> m - a) [sW', sW]

  -- Odd-difference split: low = floor(d/2), high = ceil(d/2)
  hLow <- newNonNegMap "hLow" rH
  hHigh <- newNonNegMap "hHigh" rH
  precondition [hLow, hHigh, dH] $ \[l, h, d] -> l + h .== d .&& l .<= h .&& h .<= l + 1 -- Make precondition to ensure left over padding on top
  wLow <- newNonNegMap "wLow" rW
  wHigh <- newNonNegMap "wHigh" rW
  precondition [wLow, wHigh, dW] $ \[l, h, d] -> l + h .== d .&& l .<= h .&& h .<= l + 1

  -- Zero interior paddings
  zH <- newConstMap "zeroH" 0 rH
  zW <- newConstMap "zeroW" 0 rW

  pad e (0 :: a) $
    Padding
      { low = [hRef --> hLow, wRef --> wLow],
        interior = [hRef --> zH, wRef --> zW], -- No internal padding
        high = [hRef --> hHigh, wRef --> wHigh]
      }

-- | TASO's 2D matrix multiplication operator
matmul2D ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The left-hand side tensor (shape [M, K])
  lhs ->
  -- | The right-hand side tensor (shape [K, N])
  rhs ->
  DSLContext (Expr, MapIdentifier)
matmul2D = matmul2DHelper