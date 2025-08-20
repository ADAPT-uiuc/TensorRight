{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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
    transposeSingleton,
  )
where

import TensorRight (NumBinOp (Add, Mul), ToElem, concatTensor, posInf)
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL (DSLContext, Expr, ExprInContext, RClassRef, ValidNum, clampScalar, numBinOp, numBinScalarOp, transpose2D, transpose2DSingleton)
-- import TensorRight.Internal.DSL.Expr (Expr (Pad))
-- import TensorRight.Internal.DSL.Parameters (ParamDesc)
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

transposeSingleton ::
  (ExprInContext e) =>
  -- | The tensor to transpose
  e ->
  DSLContext Expr
transposeSingleton = transpose2DSingleton

-- -- -- | TASO's enlarge operator
-- enlarge ::
--   (ExprInContext e, ToElem v, ToDType v) =>
--   -- | The tensor to enlarge.
--   e ->
--   [ParamDesc] ->
--   DSLContext Expr
-- enlarge e descs = pad