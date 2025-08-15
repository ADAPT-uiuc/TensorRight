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

module TensorRight.Internal.DSL.TASO
  ( ewadd,
    ewmul,
    smul,
    relu,
  )
where

import TensorRight (NumBinOp (Add, Mul), ToElem, posInf)
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL (DSLContext, Expr, ExprInContext, ValidNum, clampScalar, numBinOp, numBinScalarOp)

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