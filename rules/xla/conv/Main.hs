module Main (main) where

import Data.Proxy
import qualified Data.Text as T
import Grisette hiding (dot, (-->))
import TensorRight

rule00 :: forall a. NumRule a
rule00 _ = do
  [batch, feature, output, spatial] <-
    newRClasses ["batch", "feature", "output", "spatial"]

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
  ldilation <- newConstMap "ldilation" 1 spatial
  rdilation <- newMap "rdilation" spatial
  [plow, phigh] <- newNonNegMaps ["plow", "phigh"] spatial
  pint <- newMap "pint" spatial
  newlow <- sumMap "newlow" [low, plow]
  newint <- combineMap "newlow" (\[a, b] -> a + b) [ldilation, pint]
  newhigh <- combineMap "newhigh" sum [high, phigh]

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
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
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
  monitorMapOnFailure "plow" (ByRClass spatial) plow
  monitorMapOnFailure "pint" (ByRClass spatial) pint
  monitorMapOnFailure "phigh" (ByRClass spatial) phigh
  monitorMapOnFailure "low" (ByRClass spatial) low
  monitorMapOnFailure "ldilation" (ByRClass spatial) ldilation
  monitorMapOnFailure "high" (ByRClass spatial) high

  monitorMapOnFailure "newlow" (ByRClass spatial) newlow
  monitorMapOnFailure "newint" (ByRClass spatial) newint
  monitorMapOnFailure "newhigh" (ByRClass spatial) newhigh
  monitorMapOnFailure "rdilation" (ByRClass spatial) rdilation

  rhs <-
    conv
      inputs
      weights
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [feature --> siMapRhsFeature, spatial --> siMapRhsSpatial]
        }
      ConvPadding
        { low = [spatial --> newlow],
          ldilation = [spatial --> newint],
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
        [ "Conv(Pad(input, innerLow, innerInt, innerHigh), weights, convLow, 1, convHigh, rdilation)",
          " ⇒ ",
          "Conv(input, weights, convLow + innerLow, innerInt + 1, convHigh + innerHigh, rdilation)"
        ]
    )
    lhs
    rhs

rule01 :: forall a. NumRule a
rule01 _ = do
  [batch, feature, output, spatial] <-
    newRClasses ["batch", "feature", "output", "spatial"]

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
  [convLow, convHigh] <- newNonNegMaps ["convLow", "convHigh"] spatial
  ldilation <- newConstMap "ldilation" 1 spatial
  [innerLow, innerHigh] <- newConstMaps ["innerLow", "innerHigh"] 0 spatial
  innerInt <- newMap "innerInt" spatial
  lhsRdilation <- newConstMap "lhsRdilation" 1 spatial
  rhsRdilation <- combineMap "rhsRdilation" sum [lhsRdilation, innerInt]

  [siMapLhsFeature, siMapRhsFeature] <-
    newMaps ["siMapLhsFeature", "siMapRhsFeature"] feature
  [siMapLhsSpatial, siMapRhsSpatial] <-
    newMaps ["siMapLhsSpatial", "siMapRhsSpatial"] spatial

  lhsWeightPadded <-
    pad weights (0 :: a) $
      Padding
        { low = [spatial --> innerLow],
          interior = [spatial --> innerInt],
          high = [spatial --> innerHigh]
        }
  lhs <-
    conv
      inputs
      lhsWeightPadded
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [feature --> siMapLhsFeature, spatial --> siMapLhsSpatial]
        }
      ConvPadding
        { low = [spatial --> convLow],
          ldilation = [spatial --> ldilation],
          high = [spatial --> convHigh],
          rdilation = [spatial --> lhsRdilation]
        }

  rhs <-
    conv
      inputs
      weights
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [feature --> siMapRhsFeature, spatial --> siMapRhsSpatial]
        }
      ConvPadding
        { low = [spatial --> convLow],
          ldilation = [spatial --> ldilation],
          high = [spatial --> convHigh],
          rdilation = [spatial --> rhsRdilation]
        }

  siRelation
    [siMapLhsFeature, siMapRhsFeature]
    $ \[vsiMapLhsFeature, vsiMapRhsFeature] -> vsiMapLhsFeature .== vsiMapRhsFeature
  siRelation
    [siMapLhsSpatial, siMapRhsSpatial]
    $ \[vsiMapLhsSpatial, vsiMapRhsSpatial] -> vsiMapLhsSpatial .== vsiMapRhsSpatial
  checkSIMap
    [siMapLhsFeature, siMapLhsSpatial]
    [siMapRhsFeature, siMapRhsSpatial]
  rewrite
    ( T.intercalate
        "\n"
        [ "Conv(input, Pad(weights, 0, innerInt, 0), stride=1, convLow, ldilation, convHigh, 1)",
          " ⇒ ",
          "Conv(input, weights, stride=1, convLow, ldilation, convHigh, innerInt + 1)"
        ]
    )
    lhs
    rhs

{-
-- Skipped because the set being reduced in lhs and rhs are different
rule02 :: forall a. NumRule a
rule02 _ = do
  [batch, feature, output, spatial] <-
    newRClasses ["batch", "feature", "output", "spatial"]

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
  [low, high, ldilation, rdilation] <-
    newMaps ["low", "high", "ldilation", "rdilation"] spatial
  strides <- newConstMap "strides" 1 spatial

  dilatedKernelSize <-
    combineMap
      "dilatedKernelSize"
      (\[w, r] -> 1 + r * (w - 1))
      [weightSpatialShape, rdilation]
  dilatedInputSize <-
    combineMap
      "dilatedInputSize"
      (\[w, r] -> 1 + r * (w - 1))
      [inputSpatialShape, ldilation]
  newlow <-
    combineMap
      "newlow"
      (\[low, di, dk] -> low + di - dk)
      [low, dilatedInputSize, dilatedKernelSize]
  newhigh <-
    combineMap
      "newhigh"
      (\[high, di, dk] -> high + dk - di)
      [high, dilatedInputSize, dilatedKernelSize]
  newldilation <- combineMap "newldilation" head [rdilation]
  newrdilation <- combineMap "newrdilation" head [ldilation]

  newstrides <- newConstMap "newstrides" 1 spatial

  [siMapLhsFeature, siMapRhsFeature] <-
    newMaps ["siMapLhsFeature", "siMapRhsFeature"] feature
  [siMapLhsSpatial, siMapRhsSpatial] <-
    newMaps ["siMapLhsSpatial", "siMapRhsSpatial"] spatial

  lhs <-
    conv
      inputs
      weights
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
          strides = [spatial --> strides],
          contractingSIMaps =
            [ feature --> siMapLhsFeature,
              spatial --> siMapLhsSpatial
            ]
        }
      ConvPadding
        { low = [spatial --> low],
          ldilation = [spatial --> ldilation],
          high = [spatial --> high],
          rdilation = [spatial --> rdilation]
        }
  rhs <-
    conv
      (reverseTensor weights [ByRClass spatial])
      (reverseTensor inputs [ByRClass spatial])
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass output],
          outputFeatureRClasses = [ByRClass feature],
          strides = [spatial --> newstrides],
          contractingSIMaps =
            [ feature --> siMapRhsFeature,
              spatial --> siMapRhsSpatial
            ]
        }
      ConvPadding
        { low = [spatial --> newlow],
          ldilation = [spatial --> newldilation],
          high = [spatial --> newhigh],
          rdilation = [spatial --> newrdilation]
        }

  siRelation [siMapLhsFeature, siMapRhsFeature] $
    \[vsiMapLhsFeature, vsiMapRhsFeature] ->
      vsiMapLhsFeature .== vsiMapRhsFeature

  rewrite
    ( "Conv(input, weights, stride, low, ldilation, high, rdilation) "
        <> "⇒"
        <> " Conv(weights, input, stride, newlow, newldilation, newhigh, newrdilation)"
    )
    lhs
    rhs
    -}

rule03 :: forall a. NumRule a
rule03 _ = do
  [batch, feature, output, spatialTrivial, spatialOne] <-
    newRClasses ["batch", "feature", "output", "spatialTrivial", "spatialOne"]

  batchShape <- newMap "batchShape" batch
  featureShape <- newMap "featureShape" feature
  outputShape <- newMap "outputShape" output
  spatialTrivialShape <- newMap "spatialTrivialShape" spatialTrivial
  inputSpatialOneShape <- newMap "inputSpatialOneShape" spatialOne
  weightSpatialOneShape <- newConstMap "weightSpatialOneShape" 1 spatialOne

  inputs <-
    newTensor @a
      "inputs"
      [ batch --> batchShape,
        feature --> featureShape,
        spatialTrivial --> spatialTrivialShape,
        spatialOne --> inputSpatialOneShape
      ]
  weights <-
    newTensor @a
      "weights"
      [ feature --> featureShape,
        output --> outputShape,
        spatialTrivial --> spatialTrivialShape,
        spatialOne --> weightSpatialOneShape
      ]
  [lowTrivial, highTrivial] <- newConstMaps ["low", "high"] 0 spatialTrivial
  [ldilationTrivial, rdilationTrivial] <-
    newConstMaps ["ldilation", "rdilation"] 1 spatialTrivial
  stridesTrivial <- newConstMap "strides" 1 spatialTrivial

  [lowOne, highOne] <- newConstMaps ["low", "high"] 0 spatialOne
  [ldilationOne, rdilationOne] <-
    newConstMaps ["ldilation", "rdilation"] 1 spatialOne
  stridesOne <- newConstMap "strides" 1 spatialOne

  [siMapLhsFeature, siMapRhsFeature] <-
    newMaps ["siMapLhsFeature", "siMapRhsFeature"] feature
  [siMapLhsSpatialTrivial, siMapRhsSpatialTrivial] <-
    newMaps
      ["siMapLhsSpatialTrivial", "siMapRhsSpatialTrivial"]
      spatialTrivial
  [siMapLhsSpatialOne] <-
    newMaps ["siMapLhsSpatialOne"] spatialOne

  lhs <-
    conv
      inputs
      weights
      ConvConfig
        { batchRClasses = [ByRClass batch],
          featureRClasses = [ByRClass feature],
          outputFeatureRClasses = [ByRClass output],
          strides =
            [ spatialTrivial --> stridesTrivial,
              spatialOne --> stridesOne
            ],
          contractingSIMaps =
            [ feature --> siMapLhsFeature,
              spatialTrivial --> siMapLhsSpatialTrivial,
              spatialOne --> siMapLhsSpatialOne
            ]
        }
      ConvPadding
        { low = [spatialTrivial --> lowTrivial, spatialOne --> lowOne],
          ldilation = [spatialTrivial --> ldilationTrivial, spatialOne --> ldilationOne],
          high = [spatialTrivial --> highTrivial, spatialOne --> highOne],
          rdilation = [spatialTrivial --> rdilationTrivial, spatialOne --> rdilationOne]
        }

  weightExcludeSpatialOne <- reshapeDegenerate weights [] [ByRClass spatialOne]
  weightBroadcastSpatialOne <-
    broadcast weightExcludeSpatialOne [spatialOne --> inputSpatialOneShape]
  rhs <-
    reshapeDegenerate
      ( dot
          inputs
          weightBroadcastSpatialOne
          [ spatialTrivial --> siMapRhsSpatialTrivial,
            feature --> siMapRhsFeature
          ]
          [ByRClass spatialOne]
      )
      [(ByRClass spatialTrivial, spatialTrivial)]
      []
  siRelation [siMapLhsFeature, siMapRhsFeature] $
    \[vsiMapLhsFeature, vsiMapRhsFeature] ->
      vsiMapLhsFeature .== vsiMapRhsFeature
  siRelation [siMapLhsSpatialTrivial, siMapRhsSpatialTrivial] $
    \[vsiMapLhsSpatialTrivial, vsiMapRhsSpatialTrivial] ->
      vsiMapLhsSpatialTrivial .== vsiMapRhsSpatialTrivial
  siRelation [siMapLhsSpatialOne] $ \[vsiMapLhsSpatialOne] ->
    vsiMapLhsSpatialOne .== 0
  checkSIMap
    [siMapLhsFeature, siMapLhsSpatialTrivial, siMapLhsSpatialOne]
    [siMapRhsFeature, siMapRhsSpatialTrivial]
  monitorExprOnFailure "rhs" rhs
  monitorMapOnFailure "lso" (ByRClass spatialOne) siMapLhsSpatialOne
  monitorMapOnFailure "lst" (ByRClass spatialTrivial) siMapLhsSpatialTrivial
  monitorMapOnFailure "rst" (ByRClass spatialTrivial) siMapRhsSpatialTrivial

  rewrite "Conv(A,B) ⇒ Dot(A, B)" lhs rhs

main :: IO ()
main = do
  print "############################## rule00 ##############################"
  verifyNumDSL rule00
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
