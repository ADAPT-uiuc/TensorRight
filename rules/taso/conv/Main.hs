module Main (main) where

import Data.Proxy
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (ConvConfig (..), ConvPadding (..), Padding (..), checkSIMap, combineMap, monitorExprOnFailure, newConstMap, newNonNegMap, newSingletonRClass, newSingletonRClasses, pad, precondition, siRelation)
import TensorRight.Internal.DSL.Identifier (MapIdentifier, RClassIdentifier)
import TensorRight.Internal.DSL.TASO (Activation (..), PaddingMode (..), concat, enlarge, ewadd, ewmul, matmul3D, relu, smul, tasoConv)
import Prelude hiding (concat)

-- Helper to create standard 2D conv config (explicit H and W)
mkConvConfig ::
  RClassIdentifier -> -- B
  RClassIdentifier -> -- C (input feature)
  RClassIdentifier -> -- F (output feature)
  RClassIdentifier -> -- H
  RClassIdentifier -> -- W
  MapIdentifier -> -- strideH
  MapIdentifier -> -- strideW
  MapIdentifier -> -- siC
  MapIdentifier -> -- siH
  MapIdentifier -> -- siW
  ConvConfig
mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW =
  ConvConfig
    { batchRClasses = [ByRClass rclassB],
      featureRClasses = [ByRClass rclassC],
      outputFeatureRClasses = [ByRClass rclassF],
      strides = [ByRClass rclassH --> stridesH, ByRClass rclassW --> stridesW],
      contractingSIMaps = [ByRClass rclassC --> siC, ByRClass rclassH --> siH, ByRClass rclassW --> siW]
    }

-- | Rule 1: Convolution bilinearity - scalar multiplication swaps between input and kernel
convBilinearScalarSwapSame :: forall a. NumRule a
convBilinearScalarSwapSame _ = do
  let w = ("w" :: a)
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  xw <- smul x w
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Same None inputSizes kernelSizes xw y

  yw <- smul y w
  rhs <- tasoConv @a config Same None inputSizes kernelSizes x yw

  rewrite "∀s, p, c, x, y, w. conv(s, p, c, smul(x, w), y) = conv(s, p, c, x, smul(y, w))" lhs rhs

-- | Rule 1: Convolution bilinearity - scalar multiplication swaps between input and kernel
convBilinearScalarSwapValid :: forall a. NumRule a
convBilinearScalarSwapValid _ = do
  let w = ("w" :: a)
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  xw <- smul x w
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Valid None inputSizes kernelSizes xw y

  yw <- smul y w
  rhs <- tasoConv @a config Valid None inputSizes kernelSizes x yw

  rewrite "∀s, p, c, x, y, w. conv(s, p, c, smul(x, w), y) = conv(s, p, c, x, smul(y, w))" lhs rhs

-- | Rule 2: Convolution bilinearity - scalar multiplication on output
convBilinearScalarOutputSame :: forall a. NumRule a
convBilinearScalarOutputSame _ = do
  let w = ("w" :: a)
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXY <- tasoConv @a config Same None inputSizes kernelSizes x y
  lhs <- smul convXY w

  xw <- smul x w
  rhs <- tasoConv @a config Same None inputSizes kernelSizes xw y

  rewrite "∀s, p, x, y, w. smul(conv(s, p, Anone, x, y), w) = conv(s, p, Anone, smul(x, w), y)" lhs rhs

-- | Rule 2: Convolution bilinearity - scalar multiplication on output
convBilinearScalarOutputValid :: forall a. NumRule a
convBilinearScalarOutputValid _ = do
  let w = ("w" :: a)
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXY <- tasoConv @a config Valid None inputSizes kernelSizes x y
  lhs <- smul convXY w

  xw <- smul x w
  rhs <- tasoConv @a config Valid None inputSizes kernelSizes xw y

  rewrite "∀s, p, x, y, w. smul(conv(s, p, Anone, x, y), w) = conv(s, p, Anone, smul(x, w), y)" lhs rhs

-- | Rule 3: Convolution bilinearity - addition on kernel
convBilinearKernelAddSame :: forall a. NumRule a
convBilinearKernelAddSame _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  yz <- ewadd y z
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Same None inputSizes kernelSizes x yz

  convXY <- tasoConv @a config Same None inputSizes kernelSizes x y
  convXZ <- tasoConv @a config Same None inputSizes kernelSizes x z
  rhs <- ewadd convXY convXZ

  rewrite "∀s, p, x, y, z. conv(s, p, Anone, x, ewadd(y, z)) = ewadd(conv(s, p, Anone, x, y), conv(s, p, Anone, x, z))" lhs rhs

-- | Rule 3: Convolution bilinearity - addition on kernel
convBilinearKernelAddValid :: forall a. NumRule a
convBilinearKernelAddValid _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  yz <- ewadd y z
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Valid None inputSizes kernelSizes x yz

  convXY <- tasoConv @a config Valid None inputSizes kernelSizes x y
  convXZ <- tasoConv @a config Valid None inputSizes kernelSizes x z
  rhs <- ewadd convXY convXZ

  rewrite "∀s, p, x, y, z. conv(s, p, Anone, x, ewadd(y, z)) = ewadd(conv(s, p, Anone, x, y), conv(s, p, Anone, x, z))" lhs rhs

-- | Rule 4: Convolution bilinearity - addition on input
convBilinearInputAddSame :: forall a. NumRule a
convBilinearInputAddSame _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  xy <- ewadd x y
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Same None inputSizes kernelSizes xy z

  convXZ <- tasoConv @a config Same None inputSizes kernelSizes x z
  convYZ <- tasoConv @a config Same None inputSizes kernelSizes y z
  rhs <- ewadd convXZ convYZ

  rewrite "∀s, p, x, y, z. conv(s, p, Anone, ewadd(x, y), z) = ewadd(conv(s, p, Anone, x, z), conv(s, p, Anone, y, z))" lhs rhs

-- | Rule 4: Convolution bilinearity - addition on input
convBilinearInputAddValid :: forall a. NumRule a
convBilinearInputAddValid _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  xy <- ewadd x y
  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Valid None inputSizes kernelSizes xy z

  convXZ <- tasoConv @a config Valid None inputSizes kernelSizes x z
  convYZ <- tasoConv @a config Valid None inputSizes kernelSizes y z
  rhs <- ewadd convXZ convYZ

  rewrite "∀s, p, x, y, z. conv(s, p, Anone, ewadd(x, y), z) = ewadd(conv(s, p, Anone, x, z), conv(s, p, Anone, y, z))" lhs rhs

-- | Rule 5: Convolution with SAME padding and kernel enlarge (2D)
convSameEnlarge :: forall a. NumRule a
convSameEnlarge _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config =
        ConvConfig
          { batchRClasses = [ByRClass rclassB],
            featureRClasses = [ByRClass rclassC],
            outputFeatureRClasses = [ByRClass rclassF],
            strides = [ByRClass rclassH --> stridesH, ByRClass rclassW --> stridesW],
            contractingSIMaps = [ByRClass rclassC --> siC, ByRClass rclassH --> siH, ByRClass rclassW --> siW]
          }

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Same None inputSizes kernelSizes x y

  -- Enlarge kernel along H and W using built-in 2D enlarge
  hLow <- newNonNegMap "hLow" rclassH
  wLow <- newNonNegMap "wLow" rclassW
  let kHy = ssym "kHy" :: SymInteger
  let kWx = ssym "kWx" :: SymInteger
  yEnlarged <- enlarge @a (ByRClass rclassH --> kernelH) (ByRClass rclassW --> kernelW) hLow wLow kHy kWx y

  -- Compute enlarged kernel size maps (max with kHy/kWx) for SAME conv sizes
  kHMap <- newConstMap "kHMap" kHy rclassH
  kWMap <- newConstMap "kWMap" kWx rclassW
  precondition [kHMap] $ \[k] -> k .>= 0
  precondition [kWMap] $ \[k] -> k .>= 0
  kernelH' <- combineMap "kernelH'" (\[s, k] -> symIte (s .>= k) s k) [kernelH, kHMap]
  kernelW' <- combineMap "kernelW'" (\[s, k] -> symIte (s .>= k) s k) [kernelW, kWMap]
  let kernelSizesRHS = [ByRClass rclassH --> kernelH', ByRClass rclassW --> kernelW']
  rhs <- tasoConv @a config Same None inputSizes kernelSizesRHS x yEnlarged

  rewrite "conv(SAME, x, y) = conv(SAME, x, enlargeKernel2D(y))" lhs rhs

-- convIdentitySame :: forall a. NumRule a
-- convIdentitySame _ = do
--   -- RClasses: batch, channel/feature (shared!), spatial H/W
--   [rclassB, rclassCF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassCF", "rclassH", "rclassW"]

--   -- Size maps
--   sizeB <- newMap "sizeB" rclassB
--   sizeCF <- newMap "sizeCF" rclassCF -- ONE map for both input C and output F
--   inputH <- newMap "inputH" rclassH
--   inputW <- newMap "inputW" rclassW
--   kernelH <- newMap "kernelH" rclassH
--   kernelW <- newMap "kernelW" rclassW

--   -- Input tensor [B, CF, H, W]
--   x <- newTensor @a "x" [rclassB --> sizeB, rclassCF --> sizeCF, rclassH --> inputH, rclassW --> inputW]

--   -- Strides and SI maps
--   stridesH <- newMap "stridesH" rclassH
--   stridesW <- newMap "stridesW" rclassW
--   siCF <- newMap "siCF" rclassCF -- ONE SI map for channel/feature
--   siH <- newMap "siH" rclassH
--   siW <- newMap "siW" rclassW

--   let config =
--         ConvConfig
--           { batchRClasses = [ByRClass rclassB],
--             featureRClasses = [ByRClass rclassCF], -- Same RClass for input/output!
--             outputFeatureRClasses = [ByRClass rclassCF], -- Same RClass for input/output!
--             strides = [ByRClass rclassH --> stridesH, ByRClass rclassW --> stridesW],
--             contractingSIMaps = [ByRClass rclassCF --> siCF, ByRClass rclassH --> siH, ByRClass rclassW --> siW]
--           }

--   -- SAME padding + stride=1 preconditions
--   precondition [stridesH] $ \[s] -> s .== 1
--   precondition [stridesW] $ \[s] -> s .== 1

--   -- Odd kernel sizes via centers: k = 2*c + 1
--   let cH = ssym "centerH" :: SymInteger
--   let cW = ssym "centerW" :: SymInteger
--   precondition [kernelH] $ \[k] -> k .== (2 * cH + 1)
--   precondition [kernelW] $ \[k] -> k .== (2 * cW + 1)

--   -- Build explicit identity kernel: 1 when (CF_out==CF_in && H==cH && W==cW), else 0
--   -- Since kernel has rclassCF twice, we MUST use labels to disambiguate
--   let kShape = [rclassCF --> sizeCF @@ "CFout", rclassCF --> sizeCF @@ "CFin", rclassH --> kernelH, rclassW --> kernelW]
--   iCF_out <- iota kShape (ByLabel "CFout") -- Output feature index
--   iCF_in <- iota kShape (ByLabel "CFin") -- Input feature index
--   iH <- iota kShape (ByRClass rclassH)
--   iW <- iota kShape (ByRClass rclassW)

--   cHTensor <- constant @TensorInt (nonInf cH) kShape
--   cWTensor <- constant @TensorInt (nonInf cW) kShape

--   condCF <- compareOp Eqv iCF_out iCF_in -- Diagonal: channel i maps to channel i
--   condH <- compareOp Eqv iH cHTensor
--   condW <- compareOp Eqv iW cWTensor
--   condHW <- boolBinOp And condH condW
--   condAll <- boolBinOp And condCF condHW

--   one <- constant @a 1 kShape
--   zero <- constant @a 0 kShape
--   idKernel <- select condAll one zero

--   let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
--   let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]

--   lhs <- tasoConv @a config Same None inputSizes kernelSizes x idKernel
--   let rhs = x -- No transformation needed! Shapes already match: [B, CF, H, W]
--   rewrite "∀x. conv(SAME, stride=1; identity-kernel) = x" lhs rhs

-- | Rule 6: Convolution with ReLU activation
convReluActivation :: forall a. NumRule a
convReluActivation _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  lhs <- tasoConv @a config Valid Relu inputSizes kernelSizes x y

  convXY <- tasoConv @a config Valid None inputSizes kernelSizes x y
  rhs <- relu @a convXY

  rewrite "∀s, p, x, y. conv(s, p, Arelu, x, y) = relu(conv(s, p, Anone, x, y))" lhs rhs

-- | Rule 7: Concatenation along batch dimension distributes over conv
convConcatInputBatchSame :: forall a. NumRule a
convConcatInputBatchSame _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXZ <- tasoConv @a config Same None inputSizes kernelSizes x z
  convYZ <- tasoConv @a config Same None inputSizes kernelSizes y z
  lhs <- concat (ByRClass rclassB) convXZ convYZ

  xy <- concat (ByRClass rclassB) x y
  rhs <- tasoConv @a config Same None inputSizes kernelSizes xy z

  rewrite "∀s, p, c, x, y, z. concat(0, conv(s, p, c, x, z), conv(s, p, c, y, z)) = conv(s, p, c, concat(0, x, y), z)" lhs rhs

-- | Rule 7: Concatenation along batch dimension distributes over conv
convConcatInputBatchValid :: forall a. NumRule a
convConcatInputBatchValid _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  sizeF <- newMap "sizeF" rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  z <- newTensor @a "z" [rclassF --> sizeF, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXZ <- tasoConv @a config Valid None inputSizes kernelSizes x z
  convYZ <- tasoConv @a config Valid None inputSizes kernelSizes y z
  lhs <- concat (ByRClass rclassB) convXZ convYZ

  xy <- concat (ByRClass rclassB) x y
  rhs <- tasoConv @a config Valid None inputSizes kernelSizes xy z

  rewrite "∀s, p, c, x, y, z. concat(0, conv(s, p, c, x, z), conv(s, p, c, y, z)) = conv(s, p, c, concat(0, x, y), z)" lhs rhs

-- | Rule 8: Concatenation along output feature dimension distributes over conv
convConcatKernelSame :: forall a. NumRule a
convConcatKernelSame _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  [sizeF1, sizeF2] <- newMaps ["sizeF1", "sizeF2"] rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF1, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]
  z <- newTensor @a "z" [rclassF --> sizeF2, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXY <- tasoConv @a config Same None inputSizes kernelSizes x y
  convXZ <- tasoConv @a config Same None inputSizes kernelSizes x z
  lhs <- concat (ByRClass rclassF) convXY convXZ

  yz <- concat (ByRClass rclassF) y z
  rhs <- tasoConv @a config Same None inputSizes kernelSizes x yz

  rewrite "∀s, p, c, x, y, z. concat(1, conv(s, p, c, x, y), conv(s, p, c, x, z)) = conv(s, p, c, x, concat(0, y, z))" lhs rhs

-- | Rule 8: Concatenation along output feature dimension distributes over conv
convConcatKernelValid :: forall a. NumRule a
convConcatKernelValid _ = do
  [rclassB, rclassC, rclassF, rclassH, rclassW] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassH", "rclassW"]
  sizeC <- newMap "sizeC" rclassC
  [sizeF1, sizeF2] <- newMaps ["sizeF1", "sizeF2"] rclassF
  inputH <- newMap "inputH" rclassH
  inputW <- newMap "inputW" rclassW
  kernelH <- newMap "kernelH" rclassH
  kernelW <- newMap "kernelW" rclassW
  sizeB <- newMap "sizeB" rclassB

  x <- newTensor @a "x" [rclassB --> sizeB, rclassC --> sizeC, rclassH --> inputH, rclassW --> inputW]
  y <- newTensor @a "y" [rclassF --> sizeF1, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]
  z <- newTensor @a "z" [rclassF --> sizeF2, rclassC --> sizeC, rclassH --> kernelH, rclassW --> kernelW]

  stridesH <- newMap "stridesH" rclassH
  stridesW <- newMap "stridesW" rclassW
  siC <- newMap "siC" rclassC
  siH <- newMap "siH" rclassH
  siW <- newMap "siW" rclassW

  let config = mkConvConfig rclassB rclassC rclassF rclassH rclassW stridesH stridesW siC siH siW

  let inputSizes = [ByRClass rclassH --> inputH, ByRClass rclassW --> inputW]
  let kernelSizes = [ByRClass rclassH --> kernelH, ByRClass rclassW --> kernelW]
  convXY <- tasoConv @a config Valid None inputSizes kernelSizes x y
  convXZ <- tasoConv @a config Valid None inputSizes kernelSizes x z
  lhs <- concat (ByRClass rclassF) convXY convXZ

  yz <- concat (ByRClass rclassF) y z
  rhs <- tasoConv @a config Valid None inputSizes kernelSizes x yz

  rewrite "∀s, p, c, x, y, z. concat(1, conv(s, p, c, x, y), conv(s, p, c, x, z)) = conv(s, p, c, x, concat(0, y, z))" lhs rhs

-- | Rule 9: Concatenation on input channels with matching concatenation on kernel features
-- convConcatMixed :: forall a. NumRule a
-- convConcatMixed _ = do
--   [rclassB, rclassC, rclassF, rclassSpatial] <- newSingletonRClasses ["rclassB", "rclassC", "rclassF", "rclassSpatial"]
--   [sizeC1, sizeC2] <- newMaps ["sizeC1", "sizeC2"] rclassC
--   sizeF <- newMap "sizeF" rclassF
--   inputSpatial <- newMap "inputSpatial" rclassSpatial
--   kernelSpatial <- newMap "kernelSpatial" rclassSpatial
--   [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

--   x <- newTensor @a "x" [rclassB --> sizeB1, rclassC --> sizeC1, rclassSpatial --> inputSpatial]
--   z <- newTensor @a "z" [rclassB --> sizeB2, rclassC --> sizeC2, rclassSpatial --> inputSpatial]
--   y <- newTensor @a "y" [rclassF --> sizeF, rclassC --> sizeC1, rclassSpatial --> kernelSpatial]
--   w <- newTensor @a "w" [rclassF --> sizeF, rclassC --> sizeC2, rclassSpatial --> kernelSpatial]

--   strides <- newMap "strides" rclassSpatial
--   siSpatial <- newMap "siSpatial" rclassSpatial

--   let inputSizes = [ByRClass rclassSpatial --> inputSpatial]
--   let kernelSizes = [ByRClass rclassSpatial --> kernelSpatial]

--   -- LHS: concat on channels then convolve with one SI map
--   xz <- concat (ByRClass rclassC) x z
--   yw <- concat (ByRClass rclassC) y w
--   siC_LHS <- newMap "siC_LHS" rclassC
--   let configLHS = mkConvConfig rclassB rclassC rclassF rclassSpatial strides siC_LHS siSpatial
--   lhs <- tasoConv @a configLHS Valid None inputSizes kernelSizes xz yw

--   -- RHS: separate convs with separate SI maps, then add
--   siC_RHS1 <- newMap "siC_RHS1" rclassC
--   siC_RHS2 <- newMap "siC_RHS2" rclassC
--   let configRHS1 = mkConvConfig rclassB rclassC rclassF rclassSpatial strides siC_RHS1 siSpatial
--   let configRHS2 = mkConvConfig rclassB rclassC rclassF rclassSpatial strides siC_RHS2 siSpatial
--   convXY <- tasoConv @a configRHS1 Valid None inputSizes kernelSizes x y
--   convZW <- tasoConv @a configRHS2 Valid None inputSizes kernelSizes z w
--   rhs <- ewadd convXY convZW

--   -- SI relation: LHS channel SI maps to the same value in both RHS convs
--   siRelation [siC_LHS, siC_RHS1] $ \[l, r] -> l .== r
--   siRelation [siC_LHS, siC_RHS2] $ \[l, r] -> l .== r
--   checkSIMap [siC_LHS] [siC_RHS1, siC_RHS2]

--   rewrite "concat on channels splits convolution" lhs rhs

main :: IO ()
main = do
  printTitle "#################### convBilinearScalarSwapSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearScalarSwapSame

  printTitle "#################### convBilinearScalarSwapValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearScalarSwapValid

  printTitle "#################### convBilinearScalarOutputSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearScalarOutputSame

  printTitle "#################### convBilinearScalarOutputValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearScalarOutputValid

  printTitle "#################### convBilinearKernelAddSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearKernelAddSame

  printTitle "#################### convBilinearKernelAddValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearKernelAddValid

  printTitle "#################### convBilinearInputAddSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearInputAddSame

  printTitle "#################### convBilinearInputAddValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convBilinearInputAddValid

  printTitle "#################### convSameEnlarge ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convSameEnlarge

  -- printTitle "#################### convIdentitySame ####################"
  -- verifyNumDSLWith (withTimeout 15000000 z3) convIdentitySame

  printTitle "#################### convReluActivation ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convReluActivation

  printTitle "#################### convConcatInputBatchSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convConcatInputBatchSame

  printTitle "#################### convConcatInputBatchValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convConcatInputBatchValid

  printTitle "#################### convConcatKernelSame ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convConcatKernelSame

  printTitle "#################### convConcatKernelValid ####################"
  verifyNumDSLWith (withTimeout 15000000 z3) convConcatKernelValid

-- printTitle "#################### convConcatMixed ####################"
-- verifyNumDSL convConcatMixed
