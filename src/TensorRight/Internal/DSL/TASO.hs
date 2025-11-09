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
    split0,
    split1,
    transpose,
    enlarge,
    tasoConv,
    matmul2D,
    matmul3D,
    PaddingMode (..),
    Activation (..),
  )
where

import Control.Monad.Except (MonadError (throwError))
import Grisette (SymInteger, symIte, (.&&), (.<), (.<=), (.==), (.>=))
import TensorRight (NumBinOp (Add, Mul), ToElem, posInf)
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL
  ( ConvConfig (..),
    ConvPadding (..),
    DSLContext,
    Expr,
    ExprInContext,
    Padding (..),
    RClassRef (..),
    ValidNum,
    clampScalar,
    combineMap,
    conv,
    liftInContext,
    newConstMap,
    newNonNegMap,
    numBinOp,
    numBinScalarOp,
    pad,
    precondition,
    twoRefsOf,
    threeRefsOf,
    relabel,
    dot,
    concatTensor,
  )
import TensorRight.Internal.DSL.Expr (checkMapHasRClass, getRClassByMap)
import qualified TensorRight.Internal.DSL.Expr as E
import TensorRight.Internal.DSL.Identifier (MapIdentifier)
import TensorRight.Internal.DSL.Parameters (ParamDesc (..))
import TensorRight.Internal.DSL.Syntax (ArrowSyntax ((-->)))
import Prelude hiding (concat)

data Activation = Relu | None

data PaddingMode = Same | Valid

-- Helper function to get MapIdentifier from stride ParamDesc
getStrideMap :: ParamDesc -> MapIdentifier
getStrideMap (ParamDesc _ map) = map

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
transpose e' = do
  e <- liftInContext e'
  (a, b) <- twoRefsOf e
  relabel e [a --> b, b --> a]

-- TODO: Semantics of enlarge should be implemented in TensorRight/Internal/Core
-- TASO's enlarge operator!
-- Split policy: low = floor(d/2), high = d - low, where d = max(s, k) - s per axis.
enlarge ::
  forall a e.
  (ExprInContext e, ValidNum a) =>
  -- | Size descriptor for H axis: provides the axis ref and the existing size map of A along H.
  ParamDesc ->
  -- | Size descriptor for W axis: provides the axis ref and the existing size map of A along W.
  ParamDesc ->
  -- | Pre-allocated low padding map for H.
  MapIdentifier ->
  -- | Pre-allocated low padding map for W.
  MapIdentifier ->
  -- | Target size ky for H (abstract scalar).
  SymInteger ->
  -- | Target size kx for W (abstract scalar).
  SymInteger ->
  -- | The tensor to enlarge.
  e ->
  DSLContext Expr
enlarge (ParamDesc hRef sH) (ParamDesc wRef sW) hLow wLow ky kx e = do
  rH <- getRClassByMap sH
  rW <- getRClassByMap sW
  -- Ensure provided low maps match rclasses
  checkMapHasRClass rH hLow
  checkMapHasRClass rW wLow

  -- Promote scalars
  kH <- newConstMap "kH" ky rH
  kW <- newConstMap "kW" kx rW
  precondition [kH] $ \[k] -> k .>= 0
  precondition [kW] $ \[k] -> k .>= 0

  -- Target sizes via max
  sH' <- combineMap "sH'" (\[a, k] -> symIte (a .>= k) a k) [sH, kH]
  sW' <- combineMap "sW'" (\[a, k] -> symIte (a .>= k) a k) [sW, kW]

  -- Differences
  dH <- combineMap "dH" (\[m, a] -> m - a) [sH', sH]
  dW <- combineMap "dW" (\[m, a] -> m - a) [sW', sW]

  -- Determine splits and construct high end based on them
  precondition [hLow, dH] $ \[l, d] -> (l + l) .<= d .&& d .<= (l + l + 1)
  precondition [wLow, dW] $ \[l, d] -> (l + l) .<= d .&& d .<= (l + l + 1)
  hHigh <- combineMap "hHigh" (\[d, l] -> d - l) [dH, hLow]
  wHigh <- combineMap "wHigh" (\[d, l] -> d - l) [dW, wLow]

  -- Zero interior paddings
  zH <- newConstMap "zeroH" 0 rH
  zW <- newConstMap "zeroW" 0 rW

  pad e (0 :: a) $
    Padding
      { low = [hRef --> hLow, wRef --> wLow],
        interior = [hRef --> zH, wRef --> zW],
        high = [hRef --> hHigh, wRef --> wHigh]
      }

-- | TASO's 2D matrix multiplication operator
matmul2D ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The left-hand side tensor (shape [M, K])
  lhs ->
  -- | The right-hand side tensor (shape [K, N])
  rhs ->
  -- | The contracting SI maps.
  [ParamDesc] ->
  DSLContext Expr
matmul2D lhs' rhs' contract = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  (_, _) <- twoRefsOf lhs
  (_, _) <- twoRefsOf rhs
  -- TODO: do we need to check the length of contract?
  dot lhs rhs contract []

-- | TASO's 2D matrix multiplication operator
matmul3D ::
  (ExprInContext lhs, ExprInContext rhs) =>
  -- | The left-hand side tensor (shape [M, K])
  lhs ->
  -- | The right-hand side tensor (shape [K, N])
  rhs ->
  -- | The contracting SI maps.
  [ParamDesc] ->
  -- | Batch RClasses
  [RClassRef] ->
  DSLContext Expr
matmul3D lhs' rhs' contract batch = do
  lhs <- liftInContext lhs'
  rhs <- liftInContext rhs'
  -- Get the three axes from each tensor
  (_, _, _) <- threeRefsOf lhs -- B, M, K
  (_, _, _) <- threeRefsOf rhs -- B, K, N
  -- TODO: do we need to check the length of contract and batch?
  dot lhs rhs contract batch

-- | TASO's 2D matrix multiplication operator
tasoConv ::
  forall a input weights.
  (ExprInContext input, ExprInContext weights, ValidNum a) =>
  -- | Convolution config
  ConvConfig ->
  -- | Padding config
  PaddingMode ->
  -- | Choice of activation function
  Activation ->
  -- | Input spatial size maps (per spatial RClass)
  [ParamDesc] ->
  -- | Kernel spatial size maps (per spatial RClass)
  [ParamDesc] ->
  -- | Input tensor
  input ->
  -- | The weights (kernel) tensor.
  weights ->
  DSLContext Expr
tasoConv config padConfig act inputSizePDs kernelSizePDs input weights = do
  -- Determine spatial refs from the stride descriptors in the config
  let strideRefs =
        case config of
          ConvConfig {strides = ss} -> [ref | ParamDesc ref _ <- ss]

  let toRClassId ref = case ref of
        ByRClass r -> return r
        ByLabel _ -> throwError "tasoConv requires strides specified with ByRClass refs"

  -- Build padding parameters per mode
  (lowPDs, ldilPDs, highPDs, rdilPDs) <- case padConfig of
    Valid -> do
      -- VALID: low=0, high=0, ldilation=1, rdilation=1
      lowPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              z <- newConstMap "low0" 0 r
              return (ref --> z)
          )
          strideRefs
      highPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              z <- newConstMap "high0" 0 r
              return (ref --> z)
          )
          strideRefs
      ldilPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              o <- newConstMap "ldilation1" 1 r
              return (ref --> o)
          )
          strideRefs
      rdilPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              o <- newConstMap "rdilation1" 1 r
              return (ref --> o)
          )
          strideRefs
      return (lowPDs, ldilPDs, highPDs, rdilPDs)
    Same -> do
      -- SAME: compute padding using the formula: p_total = max(0, (ceil(n_in/s) - 1) * s + k - n_in)
      -- For each spatial dimension, we need input size, kernel size, and stride
      let strideMaps = [getStrideMap pd | pd <- strides config]

      -- Use provided input/kernel size maps (deterministic SAME)
      let lookupSize :: RClassRef -> [ParamDesc] -> MapIdentifier
          lookupSize ref pds =
            case [m | ParamDesc r m <- pds, r == ref] of
              (m : _) -> m
              [] -> error "tasoConv(Same): missing spatial size map"

      let inputSizePairs = [(ref, lookupSize ref inputSizePDs) | ref <- strideRefs]
      let kernelSizePairs = [(ref, lookupSize ref kernelSizePDs) | ref <- strideRefs]

      -- Create symbolic output size maps for SAME padding
      -- For SAME padding, output_size = ceil(input_size / stride)
      outputSizePairs <-
        traverse
          ( \((ref, inputSize), strideMap) -> do
              r <- toRClassId ref
              outputSize <- newNonNegMap "outputSize" r
              -- Constrain: outputSize * stride >= inputSize (ceiling property)
              precondition [outputSize, inputSize, strideMap] $ \[out, inp, str] -> out * str .>= inp
              -- Constrain: (outputSize - 1) * stride < inputSize (minimal ceiling)
              precondition [outputSize, inputSize, strideMap] $ \[out, inp, str] -> (out - 1) * str .< inp
              return (ref, outputSize)
          )
          (zip inputSizePairs strideMaps)

      -- Compute total padding using the SAME formula
      -- p_total = max(0, (outputSize - 1) * stride + kernelSize - inputSize)
      totalPaddingPairs <-
        traverse
          ( \((ref, outputSize), (_, kernelSize), ((_, inputSize), strideMap)) -> do
              -- Compute total padding: (outputSize - 1) * stride + kernelSize - inputSize
              totalPadding <- combineMap "totalPadding" (\[out, s, k, n] -> (out - 1) * s + k - n) [outputSize, strideMap, kernelSize, inputSize]
              -- Constrain total padding to be non-negative
              precondition [totalPadding] $ \[p] -> p .>= 0
              return (ref, totalPadding)
          )
          (zip3 outputSizePairs kernelSizePairs (zip inputSizePairs strideMaps))

      -- Split total padding into low and high: low = floor(p_total / 2), high = p_total - low
      lowPairs <-
        traverse
          ( \(ref, totalPadding) -> do
              r <- toRClassId ref
              low <- newNonNegMap "sameLow" r
              -- Constrain: low + low <= totalPadding <= low + low + 1
              precondition [low, totalPadding] $ \[l, p] -> (l + l) .<= p .&& p .<= (l + l + 1)
              return (ref, low)
          )
          totalPaddingPairs

      highPairs <-
        traverse
          ( \((ref, totalPadding), (_, low)) -> do
              r <- toRClassId ref
              high <- newNonNegMap "sameHigh" r
              -- Constrain: low + high = totalPadding
              precondition [low, high, totalPadding] $ \[l, h, p] -> l + h .== p
              return (ref, high)
          )
          (zip totalPaddingPairs lowPairs)

      let lowPDs = [ref --> l | (ref, l) <- lowPairs]
      let highPDs = [ref --> h | (ref, h) <- highPairs]

      -- Unit dilations
      ldilPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              o <- newConstMap "ldilation1" 1 r
              return (ref --> o)
          )
          strideRefs
      rdilPDs <-
        traverse
          ( \ref -> do
              r <- toRClassId ref
              o <- newConstMap "rdilation1" 1 r
              return (ref --> o)
          )
          strideRefs
      return (lowPDs, ldilPDs, highPDs, rdilPDs)

  outExpr <-
    conv
      input
      weights
      config
      ConvPadding
        { low = lowPDs,
          ldilation = ldilPDs,
          high = highPDs,
          rdilation = rdilPDs
        }

  case act of
    Relu -> relu @a outExpr
    None -> return outExpr

-- | TASO's split0 operator
split0 ::
  (ExprInContext e) =>
  RClassRef ->
  e ->
  DSLContext Expr
split0 axis e' = do
  e <- liftInContext e'
  case e of
    E.Concat _ l _ d | d == axis -> return l
    E.Concat {} -> throwError "split0: expected Concat on the given axis"
    _ -> throwError "split0: input is not a Concat"

-- | TASO's split1 operator
split1 ::
  (ExprInContext e) =>
  RClassRef ->
  e ->
  DSLContext Expr
split1 axis e' = do
  e <- liftInContext e'
  case e of
    E.Concat _ _ r d | d == axis -> return r
    E.Concat {} -> throwError "split1: expected Concat on the given axis"
    _ -> throwError "split1: input is not a Concat"
