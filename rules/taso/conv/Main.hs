module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL (ConvConfig (..), DSLContext, Expr)
import qualified TensorRight.Internal.DSL.TASO as TASO

-- TASO's verifier restricts Conv2D to NCHW tensors. 'tasoConv' records the
-- corresponding rank-one rclasses and asserts padding semantics in Core.
withConv2D ::
  forall a b.
  (ToDType a) =>
  (Expr -> Expr -> ConvConfig -> DSLContext b) ->
  DSLContext b
withConv2D k = do
  [batch, inputChannel, outputChannel, height, width] <-
    newRClasses ["batch", "input-channel", "output-channel", "height", "width"]
  batchSize <- newMap "batch-size" batch
  inputChannelSize <- newMap "input-channel-size" inputChannel
  outputChannelSize <- newMap "output-channel-size" outputChannel
  inputHeight <- newMap "input-height" height
  inputWidth <- newMap "input-width" width
  kernelHeight <- newMap "kernel-height" height
  kernelWidth <- newMap "kernel-width" width
  strideHeight <- newMap "stride-height" height
  strideWidth <- newMap "stride-width" width
  siChannel <- newMap "si-channel" inputChannel
  siHeight <- newMap "si-height" height
  siWidth <- newMap "si-width" width
  input <-
    newTensor
      @a
      "input"
      [ batch --> batchSize,
        inputChannel --> inputChannelSize,
        height --> inputHeight,
        width --> inputWidth
      ]
  weights <-
    newTensor
      @a
      "weights"
      [ outputChannel --> outputChannelSize,
        inputChannel --> inputChannelSize,
        height --> kernelHeight,
        width --> kernelWidth
      ]
  k
    input
    weights
    ConvConfig
      { batchRClasses = [ByRClass batch],
        featureRClasses = [ByRClass inputChannel],
        outputFeatureRClasses = [ByRClass outputChannel],
        strides = [height --> strideHeight, width --> strideWidth],
        contractingSIMaps = [inputChannel --> siChannel, height --> siHeight, width --> siWidth]
      }

-- TASO axiom: Conv(s, p, a, smul(x, w), y) = Conv(s, p, a, x, smul(y, w)).
convScalarSwapSame :: forall a. NumRule a
convScalarSwapSame _ = withConv2D @a $ \input weights config -> do
  lhs <- TASO.tasoConv @a config TASO.Same TASO.None (TASO.smul input ("scalar" :: a)) weights
  rhs <- TASO.tasoConv @a config TASO.Same TASO.None input (TASO.smul weights ("scalar" :: a))
  rewrite "conv(same, smul(x, w), y) => conv(same, x, smul(y, w))" lhs rhs

-- TASO axiom: smul(Conv(s, p, none, x, y), w) = Conv(s, p, none, smul(x, w), y).
convScalarOutputValid :: forall a. NumRule a
convScalarOutputValid _ = withConv2D @a $ \input weights config -> do
  output <- TASO.tasoConv @a config TASO.Valid TASO.None input weights
  lhs <- TASO.smul output ("scalar" :: a)
  rhs <- TASO.tasoConv @a config TASO.Valid TASO.None (TASO.smul input ("scalar" :: a)) weights
  rewrite "smul(conv(valid, x, y), w) => conv(valid, smul(x, w), y)" lhs rhs

-- TASO axiom: relu(Conv(s, p, none, x, y)) = Conv(s, p, relu, x, y).
--
-- This is retained for the checklist but deliberately not called below:
-- TensorRight's generic clamp cannot yet consume the reduction-valued element
-- produced by convolution. A fused backend activation is required.
convReluFusion :: forall a. NumRule a
convReluFusion _ = withConv2D @a $ \input weights config -> do
  lhs <- TASO.relu @a =<< TASO.tasoConv @a config TASO.Same TASO.None input weights
  rhs <- TASO.tasoConv @a config TASO.Same TASO.Relu input weights
  rewrite "relu(conv(same, x, y)) => conv(same, relu, x, y)" lhs rhs

main :: IO ()
main = do
  verifyNumDSL convScalarSwapSame
  verifyNumDSL convScalarOutputValid
