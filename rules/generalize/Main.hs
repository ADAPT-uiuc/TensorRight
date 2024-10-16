module Main (main) where

import Data.Proxy
import qualified Data.Text as T
import Grisette hiding (dot, (-->))
import TensorRight

foldConvInputPadGeneral :: forall a. NumRule a
foldConvInputPadGeneral _ = do
  [batch, feature, output, spatial] <-
    newAdims ["batch", "feature", "output", "spatial"]

  batchShape <- newMap "batchShape" batch
  featureShape <- newMap "featureShape" feature
  outputShape <- newMap "outputShape" output
  inputSpatialShape <- newMap "inputSpatialShape" spatial
  weightSpatialShape <- newMap "weightSpatialShape" spatial

  inputs <-
    newTensor @a
      "inputs"
      [ batch --> batchShape,
        feature --> featureShape,
        spatial --> inputSpatialShape
      ]
  weights <-
    newTensor @a
      "weights"
      [ feature --> featureShape,
        output --> outputShape,
        spatial --> weightSpatialShape
      ]

  strides <- newConstMap "strides" 1 spatial
  -- Turns out that non-negative is required, even if we support negative
  -- padding. The reason is that when x contains negative indices,
  -- and x + y >= 0, then
  --
  -- pad(pad(A, x), y) /= pad(A, x + y)
  [low, high] <- newNonNegMaps ["low", "high"] spatial
  ldilation <- newNonNegMap "ldilation" spatial
  rdilation <- newNonNegMap "rdilation" spatial
  [plow, phigh] <- newNonNegMaps ["plow", "phigh"] spatial
  pint <- newNonNegMap "pint" spatial
  newlow <- combineMap "newlow" (\[a, b, c] -> a + b * c) [low, plow, ldilation]
  newldilation <- combineMap "newldilation" (\[a, b] -> a + a * b) [ldilation, pint]
  newhigh <- combineMap "newhigh" (\[a, b, c] -> a + b * c) [high, phigh, ldilation]
  precondition [inputSpatialShape] $ \[s] -> s .> 0
  precondition [weightSpatialShape] $ \[s] -> s .> 0

  [siMapLhsFeature, siMapRhsFeature] <-
    newMaps ["siMapLhsFeature", "siMapRhsFeature"] feature
  [siMapLhsSpatial, siMapRhsSpatial] <-
    newMaps ["siMapLhsSpatial", "siMapRhsSpatial"] spatial

  lhsInputsPadded <-
    pad inputs (0 :: a) $
      Padding
        { low = [spatial --> plow],
          interior = [spatial --> pint],
          high = [spatial --> phigh]
        }
  lhs <-
    conv
      lhsInputsPadded
      weights
      ConvConfig
        { batchAdims = [ByAdim batch],
          featureAdims = [ByAdim feature],
          outputFeatureAdims = [ByAdim output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [feature --> siMapLhsFeature, spatial --> siMapLhsSpatial]
        }
      ConvPadding
        { low = [spatial --> low],
          ldilation = [spatial --> ldilation],
          high = [spatial --> high],
          rdilation = [spatial --> rdilation]
        }
  monitorExprOnFailure "inputs" inputs
  monitorExprOnFailure "weights" weights
  monitorExprOnFailure "lhsInputPadded" lhsInputsPadded
  monitorExprOnFailure "lhs" lhs
  monitorMapOnFailure "plow" (ByAdim spatial) plow
  monitorMapOnFailure "pint" (ByAdim spatial) pint
  monitorMapOnFailure "phigh" (ByAdim spatial) phigh
  monitorMapOnFailure "low" (ByAdim spatial) low
  monitorMapOnFailure "ldilation" (ByAdim spatial) ldilation
  monitorMapOnFailure "high" (ByAdim spatial) high

  monitorMapOnFailure "newlow" (ByAdim spatial) newlow
  monitorMapOnFailure "newint" (ByAdim spatial) newldilation
  monitorMapOnFailure "newhigh" (ByAdim spatial) newhigh
  monitorMapOnFailure "rdilation" (ByAdim spatial) rdilation

  rhs <-
    conv
      inputs
      weights
      ConvConfig
        { batchAdims = [ByAdim batch],
          featureAdims = [ByAdim feature],
          outputFeatureAdims = [ByAdim output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [feature --> siMapRhsFeature, spatial --> siMapRhsSpatial]
        }
      ConvPadding
        { low = [spatial --> newlow],
          ldilation = [spatial --> newldilation],
          high = [spatial --> newhigh],
          rdilation = [spatial --> rdilation]
        }

  siRelation
    [siMapLhsFeature, siMapRhsFeature]
    $ \[vsiMapLhsFeature, vsiMapRhsFeature] ->
      vsiMapLhsFeature .== vsiMapRhsFeature
  siRelation
    [siMapLhsSpatial, siMapRhsSpatial]
    $ \[vsiMapLhsSpatial, vsiMapRhsSpatial] ->
      vsiMapLhsSpatial .== vsiMapRhsSpatial
  checkSIMap
    [siMapLhsFeature, siMapLhsSpatial]
    [siMapRhsFeature, siMapRhsSpatial]
  rewrite
    ( T.intercalate
        "\n"
        [ "Conv(Pad(input, innerLow, innerInt, innerHigh), weights, convLow, convInt, convHigh, rdilation)",
          " ⇒ ",
          "Conv(input, weights, convLowOut, convIntOut, convHighOut, rdilation)"
        ]
    )
    lhs
    rhs

main :: IO ()
main = do
  verifyNumDSL foldConvInputPadGeneral
