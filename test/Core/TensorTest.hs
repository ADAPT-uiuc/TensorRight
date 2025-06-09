{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Core.TensorTest (tensorTest) where

import Data.Bifunctor (Bifunctor (bimap))
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.String (IsString (fromString))
import GHC.Stack (HasCallStack)
import Grisette
  ( Apply (apply),
    EvalSym,
    ITEOp (symIte),
    LogicalOp ((.&&)),
    SimpleMergeable,
    Solvable (con, isym, ssym),
    SymBool,
    SymEq ((.==)),
    SymInteger,
    mrgReturn,
    (.!?),
    type (=~>),
  )
import TensorRight.Internal.Core.Axis
  ( Axis (Axis),
    AxisMapLike (fromKVPairs),
    Indices,
    Sizes,
    getAxis,
  )
import TensorRight.Internal.Core.Tensor.TensorInt (TensorInt, nonInf)
import TensorRight.Internal.Core.Tensor.Typed
  ( ConvConfigArgs
      ( ConvConfigArgs,
        convBatchAxes,
        convContractingSIMap,
        convFeatureAxes,
        convOutputFeatureAxes,
        convStrides
      ),
    DySliceArgs (DySliceArgs),
    NumBinOp (Add, Mul),
    PaddingArgs (PaddingArgs, highPad, interiorPad, lowPad),
    SliceArgs (SliceArgs, end, start, strides),
    Tensor (Tensor, tensorShape),
    TensorElem (TensorElemSum, TensorElemVal),
    broadcast,
    concatTensor,
    convBase,
    createTensor,
    dynamicSlice,
    dynamicUpdateSlice,
    indicesInRange,
    iota,
    numBinOp,
    pad,
    padLow,
    reduce,
    sliceStartEndStrides,
    tensorAccess,
    transpose,
  )
import TensorRight.Internal.Util.Error (ErrorEnv)
import Test.Framework (Test, testGroup)
import Test.Framework.Providers.HUnit (testCase)
import Test.HUnit ((@?=))
import TestUtil (eqWhenSuccess, isError, isNotError)

simpleTensor ::
  forall elem.
  (IsString elem, SimpleMergeable elem) =>
  String ->
  [(String, Int)] ->
  Tensor elem
simpleTensor prefix nums =
  Tensor
    ( \indices -> do
        indicesInRange size indices
        x <- linear .!? get indices 0 nums
        case x of
          Nothing -> mrgReturn $ TensorElemVal "?"
          Just x -> mrgReturn $ TensorElemVal x
    )
    size
  where
    size = fromKVPairs $ fmap (bimap (Axis . fromString) fromIntegral) nums
    go names [] = names
    go names ((name, num) : ns) = do
      v <- [0 .. num - 1]
      go (fmap (\x -> x ++ name ++ show v) names) ns
    linear = fromString <$> go [prefix] nums
    get _ last [] = last
    get indices last ((name, num) : ns) = do
      get
        indices
        (fromIntegral num * last + getAxis (Axis $ fromString name) indices)
        ns

data TensorTest elem = TensorTest
  { tensor :: ErrorEnv (Tensor elem),
    shape :: Maybe Sizes,
    access :: Maybe Indices,
    expected :: Maybe (TensorElem elem)
  }

toTensorTest ::
  (HasCallStack, EvalSym elem, Show elem, SymEq elem, SimpleMergeable elem) =>
  String ->
  TensorTest elem ->
  Test
toTensorTest name (TensorTest tensor shape access expected) =
  testCase name $
    case (access, shape) of
      (Just access, Just shape) -> do
        isNotError tensor
        (tensorShape <$> tensor) `eqWhenSuccess` shape
        let actual = tensor >>= (`tensorAccess` access)
        case expected of
          Nothing -> isError actual
          Just expected -> actual `eqWhenSuccess` expected
      (Nothing, Nothing) -> isError tensor
      _ -> error "shape, access, must be both Just or both Nothing"

tensorTest :: Test
tensorTest =
  testGroup
    "Tensor"
    [ testGroup
        "tensorAccess"
        [ testCase "in bound" $ do
            let actual =
                  tensorAccess
                    ( simpleTensor @SymInteger
                        "x"
                        [("a", 2), ("b", 3), ("c", 4)]
                    )
                    (fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)])
            actual @?= mrgReturn (TensorElemVal "xa1b2c3"),
          testCase "extra axis" $ do
            let actual =
                  tensorAccess
                    ( simpleTensor @SymInteger
                        "x"
                        [("a", 2), ("b", 3), ("c", 4)]
                    )
                    ( fromKVPairs
                        [ (Axis "a", 1),
                          (Axis "b", 2),
                          (Axis "c", 3),
                          (Axis "d", 1)
                        ]
                    )
            isError actual,
          testCase "missing axis" $ do
            let actual =
                  tensorAccess
                    (simpleTensor @SymInteger "x" [("a", 2), ("b", 3), ("c", 4)])
                    (fromKVPairs [(Axis "a", 1), (Axis "b", 2)])
            isError actual,
          testCase "out of bound" $ do
            let actual =
                  tensorAccess
                    (simpleTensor @SymInteger "x" [("a", 2), ("b", 3), ("c", 4)])
                    (fromKVPairs [(Axis "a", 2), (Axis "b", 2), (Axis "c", 3)])
            isError actual,
          testCase "boolean " $ do
            let actual =
                  tensorAccess
                    ( simpleTensor @SymBool
                        "x"
                        [("a", 2), ("b", 3), ("c", 4)]
                    )
                    (fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)])
            actual @?= mrgReturn (TensorElemVal "xa1b2c3")
        ],
      testGroup
        "createTensor'"
        [ toTensorTest "createTensor" $
            TensorTest
              { tensor =
                  createTensor @TensorInt
                    "x"
                    (fromKVPairs [(Axis "a", 5), (Axis "b", 6), (Axis "c", 7)]),
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 5), (Axis "b", 6), (Axis "c", 7)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "c", 4)],
                expected =
                  Just
                    ( TensorElemVal $
                        nonInf $
                          apply
                            (ssym "x" :: SymInteger =~> SymInteger)
                            109
                    )
              },
          toTensorTest "0 shape" $
            TensorTest
              { tensor =
                  createTensor @TensorInt
                    "x"
                    (fromKVPairs [(Axis "a", 0), (Axis "b", 3), (Axis "c", 4)]),
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 3), (Axis "c", 4)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 2), (Axis "c", 3)],
                expected = Nothing
              }
        ],
      testGroup
        "numBinOp"
        [ toTensorTest "no reduction" $
            TensorTest
              { tensor =
                  numBinOp
                    Add
                    (simpleTensor @TensorInt "x" [("a", 2), ("b", 3), ("c", 4)])
                    (simpleTensor "y" [("a", 2), ("b", 3), ("c", 4)]),
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "c", 4)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)],
                expected =
                  Just (TensorElemVal $ "xa1b2c3" + "ya1b2c3")
              },
          toTensorTest "mul left reduction" $ do
            let sia = "sia"
            TensorTest
              { tensor =
                  numBinOp
                    Mul
                    ( reduce
                        (simpleTensor @TensorInt "x" [("a", 2), ("b", 3), ("c", 4)])
                        (fromKVPairs [(Axis "a", sia)])
                    )
                    (simpleTensor "y" [("b", 3), ("c", 4)]),
                shape =
                  Just $
                    fromKVPairs [(Axis "b", 3), (Axis "c", 4)],
                access =
                  Just $ fromKVPairs [(Axis "b", 2), (Axis "c", 3)],
                expected =
                  Just
                    ( TensorElemSum
                        ( nonInf $
                            symIte
                              (sia .== 0)
                              ("xa0b2c3" * "yb2c3")
                              ("xa1b2c3" * "yb2c3")
                        )
                    )
              },
          toTensorTest "mul right reduction" $ do
            let sia = "sia"
            TensorTest
              { tensor =
                  numBinOp
                    Mul
                    (simpleTensor @TensorInt "x" [("b", 3), ("c", 4)])
                    ( reduce
                        (simpleTensor "y" [("a", 2), ("b", 3), ("c", 4)])
                        (fromKVPairs [(Axis "a", sia)])
                    ),
                shape =
                  Just $
                    fromKVPairs [(Axis "b", 3), (Axis "c", 4)],
                access =
                  Just $ fromKVPairs [(Axis "b", 2), (Axis "c", 3)],
                expected =
                  Just
                    ( TensorElemSum
                        ( nonInf $
                            symIte
                              (sia .== 0)
                              ("xb2c3" * "ya0b2c3")
                              ("xb2c3" * "ya1b2c3")
                        )
                    )
              },
          toTensorTest "mul both reduction" $ do
            let siax = "siax"
            let siay = "siay"
            TensorTest
              { tensor =
                  numBinOp
                    Mul
                    ( reduce
                        (simpleTensor @TensorInt "x" [("a", 1), ("b", 3), ("c", 4)])
                        (fromKVPairs [(Axis "a", siax)])
                    )
                    ( reduce
                        (simpleTensor "y" [("a", 2), ("b", 3), ("c", 4)])
                        (fromKVPairs [(Axis "a", siay)])
                    ),
                shape =
                  Just $
                    fromKVPairs [(Axis "b", 3), (Axis "c", 4)],
                access =
                  Just $ fromKVPairs [(Axis "b", 2), (Axis "c", 3)],
                expected =
                  Just
                    ( TensorElemSum
                        ( nonInf $
                            symIte
                              (siay .== 0)
                              ("xa0b2c3" * "ya0b2c3")
                              ("xa0b2c3" * "ya1b2c3")
                        )
                    )
              },
          toTensorTest "mismatch" $ do
            TensorTest
              { tensor =
                  numBinOp
                    Add
                    (simpleTensor @TensorInt "x" [("a", 2), ("b", 3), ("c", 4)])
                    (simpleTensor "y" [("a", 2), ("b", 3), ("c", 5)]),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
        ],
      testGroup
        "reduce"
        [ toTensorTest "reduce single" $ do
            let sia = "sia"
            TensorTest
              { tensor =
                  reduce
                    (simpleTensor @TensorInt "x" [("a", 1), ("b", 2), ("c", 2)])
                    (fromKVPairs [(Axis "a", sia)]),
                shape = Just $ fromKVPairs [(Axis "b", 2), (Axis "c", 2)],
                access = Just $ fromKVPairs [(Axis "b", 1), (Axis "c", 1)],
                expected = Just (TensorElemSum "xa0b1c1")
              },
          toTensorTest "reduce" $ do
            let sia = "sia"
            let sib = "sib"
            TensorTest
              { tensor =
                  reduce
                    (simpleTensor @TensorInt "x" [("a", 1), ("b", 2), ("c", 2)])
                    (fromKVPairs [(Axis "a", sia), (Axis "b", sib)]),
                shape = Just $ fromKVPairs [(Axis "c", 2)],
                access = Just $ fromKVPairs [(Axis "c", 1)],
                expected =
                  Just
                    ( TensorElemSum
                        (nonInf $ symIte (sia .== 0 .&& sib .== 0) "xa0b0c1" "xa0b1c1")
                    )
              },
          toTensorTest "nested" $ do
            let sia = "sia"
            let sib = "sib"
            TensorTest
              { tensor =
                  reduce
                    ( reduce
                        (simpleTensor @TensorInt "x" [("a", 1), ("b", 2), ("c", 2)])
                        (fromKVPairs [(Axis "a", sia)])
                    )
                    (fromKVPairs [(Axis "b", sib)]),
                shape = Just $ fromKVPairs [(Axis "c", 2)],
                access = Just $ fromKVPairs [(Axis "c", 1)],
                expected =
                  Just
                    ( TensorElemSum
                        (nonInf $ symIte (sia .== 0 .&& sib .== 0) "xa0b0c1" "xa0b1c1")
                    )
              },
          toTensorTest "mismatch" $ do
            let sia = "sia"
            TensorTest
              { tensor =
                  reduce
                    (simpleTensor @TensorInt "x" [("b", 2), ("c", 2)])
                    (fromKVPairs [(Axis "a", sia)]),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "mismatch2" $ do
            let sia = "sia"
            TensorTest
              { tensor =
                  reduce
                    (simpleTensor @TensorInt "x" [("a", 1), ("b", 2), ("c", 2)])
                    (fromKVPairs [(Axis "a", sia), (Axis "b", sia)]),
                shape = Just $ fromKVPairs [(Axis "c", 2)],
                access = Just $ fromKVPairs [(Axis "a", 1)],
                expected = Nothing
              }
        ],
      testGroup
        "broadcast"
        [ toTensorTest "broadcast" $ do
            let newb = "newb"
            TensorTest
              { tensor =
                  broadcast
                    (simpleTensor @SymInteger "x" [("a", 2)])
                    (fromKVPairs [(Axis "b", newb)]),
                shape = Just $ fromKVPairs [(Axis "a", 2), (Axis "b", newb)],
                access = Just $ fromKVPairs [(Axis "a", 1), (Axis "b", 2)],
                expected = Just (TensorElemVal "xa1")
              },
          toTensorTest "collide axis" $ do
            let newb = "newb"
            TensorTest
              { tensor =
                  broadcast
                    (simpleTensor @SymInteger "x" [("a", 2), ("b", 3)])
                    (fromKVPairs [(Axis "b", newb)]),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "indices do not have all axes" $ do
            let newb = "newb"
            TensorTest
              { tensor =
                  broadcast
                    (simpleTensor @SymInteger "x" [("a", 2)])
                    (fromKVPairs [(Axis "b", newb)]),
                shape = Just $ fromKVPairs [(Axis "a", 2), (Axis "b", newb)],
                access = Just $ fromKVPairs [(Axis "a", 1)],
                expected = Nothing
              },
          toTensorTest "new axes contain 0 sized dimensions" $ do
            TensorTest
              { tensor =
                  broadcast
                    (simpleTensor @SymInteger "x" [("a", 2)])
                    (fromKVPairs [(Axis "b", 0)]),
                shape = Just $ fromKVPairs [(Axis "a", 2), (Axis "b", 0)],
                access = Just $ fromKVPairs [(Axis "a", 1)],
                expected = Nothing
              }
        ],
      testGroup
        "iota"
        [ toTensorTest "iota" $ do
            let newa = "newa"
            let newb = "newb"
            TensorTest
              { tensor =
                  iota
                    (fromKVPairs [(Axis "a", newa), (Axis "b", newb)])
                    (Axis "a"),
                shape = Just $ fromKVPairs [(Axis "a", newa), (Axis "b", newb)],
                access = Just $ fromKVPairs [(Axis "a", 1), (Axis "b", 2)],
                expected = Just (TensorElemVal 1)
              },
          toTensorTest "bad axis" $ do
            let newa = "newa"
            let newb = "newb"
            TensorTest
              { tensor =
                  iota
                    (fromKVPairs [(Axis "a", newa), (Axis "b", newb)])
                    (Axis "c"),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "bad access" $ do
            let newa = "newa"
            let newb = "newb"
            TensorTest
              { tensor =
                  iota
                    (fromKVPairs [(Axis "a", newa), (Axis "b", newb)])
                    (Axis "a"),
                shape = Just $ fromKVPairs [(Axis "a", newa), (Axis "b", newb)],
                access = Just $ fromKVPairs [(Axis "a", 1)],
                expected = Nothing
              }
        ],
      testGroup "sliceStartEndStrides" $ do
        let x623 =
              simpleTensor @SymInteger
                "x"
                [("a", 6), ("b", 2), ("c", 3)]
        [ toTensorTest "slice" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1)],
                        end = fromKVPairs [(Axis "a", 5)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa3b1c2")
              },
          toTensorTest "slice range not perfect multiple of stride" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1)],
                        end = fromKVPairs [(Axis "a", 6)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 3), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa5b1c2")
              },
          toTensorTest "slice end = start" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1)],
                        end = fromKVPairs [(Axis "a", 1)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 1), (Axis "c", 2)],
                expected = Nothing
              },
          toTensorTest "slice start/end have different axes" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1), (Axis "b", 1)],
                        end = fromKVPairs [(Axis "a", 4)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 1), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 0), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa3b1c2")
              },
          toTensorTest "slice stride/end have different axes" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "b", 1)],
                        end = fromKVPairs [(Axis "a", 5)],
                        strides = fromKVPairs [(Axis "a", 2), (Axis "c", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 3), (Axis "b", 1), (Axis "c", 2)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 0), (Axis "c", 1)],
                expected = Just (TensorElemVal "xa4b1c2")
              },
          toTensorTest "slice with non-existing axes" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1), (Axis "d", 1)],
                        end = fromKVPairs [(Axis "a", 1), (Axis "d", 1)],
                        strides = fromKVPairs [(Axis "a", 2), (Axis "d", 1)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "slice end less than start" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 1)],
                        end = fromKVPairs [(Axis "a", 0)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "negative start" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", -1)],
                        end = fromKVPairs [(Axis "a", 2)],
                        strides = fromKVPairs [(Axis "a", 2)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "non-positive stride" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 0)],
                        end = fromKVPairs [(Axis "a", 2)],
                        strides = fromKVPairs [(Axis "a", 0)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "end too large" $ do
            TensorTest
              { tensor =
                  sliceStartEndStrides x623 $
                    SliceArgs
                      { start = fromKVPairs [(Axis "a", 0)],
                        end = fromKVPairs [(Axis "a", 7)],
                        strides = fromKVPairs [(Axis "a", 1)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
          ],
      testGroup
        "pad-regression"
        [ toTensorTest "access high pad, original zero sized" $ do
            let tensor = simpleTensor @SymInteger "x" [("a", 0)]
            TensorTest
              { tensor =
                  pad tensor 0 $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 0)],
                        interiorPad = fromKVPairs [(Axis "a", 0)],
                        highPad = fromKVPairs [(Axis "a", 1)]
                      },
                shape = Just $ fromKVPairs [(Axis "a", 1)],
                access = Just $ fromKVPairs [(Axis "a", 0)],
                expected = Just (TensorElemVal 0)
              },
          toTensorTest "reg2" $ do
            let tensor = simpleTensor @SymInteger "x" [("a", 1), ("b", 2)]
            TensorTest
              { tensor =
                  pad tensor 0 $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 1), (Axis "b", 0)],
                        interiorPad = fromKVPairs [(Axis "a", 0), (Axis "b", 0)],
                        highPad = fromKVPairs [(Axis "a", 0), (Axis "b", 0)]
                      },
                shape = Just $ fromKVPairs [(Axis "a", 2), (Axis "b", 2)],
                access = Just $ fromKVPairs [(Axis "a", 0), (Axis "b", 0)],
                expected = Just (TensorElemVal 0)
              }
        ],
      testGroup "padLow" $ do
        let x623 =
              simpleTensor @SymInteger
                "x"
                [("a", 6), ("b", 2), ("c", 3)]
        let padded =
              padLow x623 "m" $ fromKVPairs [(Axis "a", 7), (Axis "b", 3)]
        let paddedShape =
              fromKVPairs [(Axis "a", 13), (Axis "b", 5), (Axis "c", 3)]
        [ toTensorTest "access padded" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "m")
              },
          toTensorTest "access elem" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 8), (Axis "b", 4), (Axis "c", 0)],
                expected = Just (TensorElemVal "xa1b1c0")
              }
          ],
      testGroup "pad" $ do
        let x623 =
              simpleTensor @SymInteger
                "x"
                [("a", 6), ("b", 2), ("c", 3)]
        let padded =
              pad x623 "m" $
                PaddingArgs
                  { lowPad = fromKVPairs [(Axis "a", 1)],
                    interiorPad = fromKVPairs [(Axis "a", 2)],
                    highPad = fromKVPairs [(Axis "a", 3)]
                  }
        let paddedShape =
              fromKVPairs [(Axis "a", 20), (Axis "b", 2), (Axis "c", 3)]
        [ toTensorTest "access low pad" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 0), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "m")
              },
          toTensorTest "access inner non-padded" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa0b1c2")
              },
          toTensorTest "access inner pad 0" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "m")
              },
          toTensorTest "access inner pad 1" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 3), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "m")
              },
          toTensorTest "access inner last non-padded" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 16), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa5b1c2")
              },
          toTensorTest "access first high padded" $
            TensorTest
              { tensor = padded,
                shape = Just paddedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 17), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "m")
              },
          toTensorTest "pad nothing" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 0)],
                        interiorPad = fromKVPairs [(Axis "a", 0)],
                        highPad = fromKVPairs [(Axis "a", 0)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 6), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 5), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa5b1c2")
              },
          toTensorTest "low have different axes than interior" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 1), (Axis "b", 1)],
                        interiorPad = fromKVPairs [(Axis "a", 2)],
                        highPad = fromKVPairs [(Axis "a", 3)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 20), (Axis "b", 3), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 4), (Axis "b", 2), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa1b1c2")
              },
          toTensorTest "low have different axes than high" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 1)],
                        interiorPad = fromKVPairs [(Axis "a", 2)],
                        highPad = fromKVPairs [(Axis "a", 3), (Axis "b", 2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 20), (Axis "b", 4), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 4), (Axis "b", 1), (Axis "c", 2)],
                expected = Just (TensorElemVal "xa1b1c2")
              },
          toTensorTest "inexistent axes" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 1), (Axis "d", 2)],
                        interiorPad = fromKVPairs [(Axis "a", 2), (Axis "d", 2)],
                        highPad = fromKVPairs [(Axis "a", 3), (Axis "d", 2)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "negative low padding" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", -2)],
                        interiorPad = fromKVPairs [(Axis "a", 2)],
                        highPad = fromKVPairs [(Axis "a", 3)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 17), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 7), (Axis "b", 1), (Axis "c", 2)],
                expected = Just $ TensorElemVal "xa3b1c2"
              },
          toTensorTest "large negative low padding" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", -10)],
                        interiorPad = fromKVPairs [(Axis "a", 0)],
                        highPad = fromKVPairs [(Axis "a", 3)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest
            "large negative low padding, fixed by other paddings"
            $ TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", -10)],
                        interiorPad = fromKVPairs [(Axis "a", 0)],
                        highPad = fromKVPairs [(Axis "a", 5)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $ fromKVPairs [(Axis "a", 0), (Axis "b", 1), (Axis "c", 2)],
                expected = Just $ TensorElemVal "m"
              },
          toTensorTest "negative interior padding" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 1)],
                        interiorPad = fromKVPairs [(Axis "a", -1)],
                        highPad = fromKVPairs [(Axis "a", 3)]
                      },
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "negative high padding" $
            TensorTest
              { tensor =
                  pad x623 "m" $
                    PaddingArgs
                      { lowPad = fromKVPairs [(Axis "a", 3)],
                        interiorPad = fromKVPairs [(Axis "a", 2)],
                        highPad = fromKVPairs [(Axis "a", -2)]
                      },
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 17), (Axis "b", 2), (Axis "c", 3)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 9), (Axis "b", 1), (Axis "c", 2)],
                expected = Just $ TensorElemVal "xa2b1c2"
              }
          ],
      testGroup "transpose" $ do
        let axisa = Axis "a"
        let axisb = Axis "b"
        let axisc = Axis "c"
        let x567 =
              simpleTensor @SymInteger
                "x"
                [("a", 5), ("b", 6), ("c", 7)]
        [ toTensorTest "transpose" $ do
            TensorTest
              { tensor =
                  -- transpose(x, (2, 0, 1))
                  transpose
                    x567
                    ( HM.fromList
                        [(axisc, axisa), (axisa, axisb), (axisb, axisc)]
                    ),
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 7), (Axis "b", 5), (Axis "c", 6)],
                access =
                  Just $
                    fromKVPairs
                      [(Axis "a", 4), (Axis "b", 2), (Axis "c", 3)],
                expected = Just (TensorElemVal "xa2b3c4")
              },
          toTensorTest "not a permutation" $ do
            TensorTest
              { tensor =
                  transpose
                    x567
                    ( HM.fromList
                        [(axisa, axisc), (axisb, axisa), (axisc, axisa)]
                    ),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "not a permutation" $ do
            TensorTest
              { tensor =
                  transpose x567 (HM.fromList [(axisa, axisc), (axisb, axisa)]),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
          ],
      testGroup "concatTensor" $ do
        let concated =
              concatTensor
                (simpleTensor @SymInteger "x" [("a", 2), ("b", 3), ("c", 4)])
                (simpleTensor @SymInteger "y" [("a", 3), ("b", 3), ("c", 4)])
                (Axis "a")
        let concatedShape =
              Just $
                fromKVPairs
                  [(Axis "a", 5), (Axis "b", 3), (Axis "c", 4)]
        [ toTensorTest "access first part" $
            TensorTest
              { tensor = concated,
                shape = concatedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)],
                expected = Just (TensorElemVal "xa1b2c3")
              },
          toTensorTest "access second part" $
            TensorTest
              { tensor = concated,
                shape = concatedShape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 4), (Axis "b", 2), (Axis "c", 3)],
                expected = Just (TensorElemVal "ya2b2c3")
              },
          toTensorTest "different axes" $
            TensorTest
              { tensor =
                  concatTensor
                    (simpleTensor "x" [("a", 2), ("b", 3), ("c", 4)])
                    (simpleTensor @SymInteger "y" [("a", 3), ("b", 3)])
                    (Axis "a"),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "inexist axis" $
            TensorTest
              { tensor =
                  concatTensor
                    (simpleTensor "x" [("a", 2), ("b", 3), ("c", 4)])
                    ( simpleTensor @SymInteger
                        "y"
                        [("a", 3), ("b", 3), ("c", 4)]
                    )
                    (Axis "d"),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "different other axis" $
            TensorTest
              { tensor =
                  concatTensor
                    (simpleTensor "x" [("a", 2), ("b", 3), ("c", 4)])
                    ( simpleTensor @SymInteger
                        "y"
                        [("a", 2), ("b", 3), ("c", 3)]
                    )
                    (Axis "a"),
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
          ],
      testGroup
        "dynamicSlice"
        [ toTensorTest "dynamicSlice" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start =
                  fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)]
            let shape =
                  fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "c", 2)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Just shape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 1)],
                expected = Just $ TensorElemVal "xa2b4c4"
              },
          toTensorTest "dynamicSlice axes is subset" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start = fromKVPairs [(Axis "a", 1), (Axis "b", 2)]
            let shape = fromKVPairs [(Axis "a", 2), (Axis "b", 3)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "c", 7)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 2)],
                expected = Just $ TensorElemVal "xa2b4c2"
              },
          toTensorTest "different start/sizes axes" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start = fromKVPairs [(Axis "a", 1), (Axis "b", 2)]
            let shape = fromKVPairs [(Axis "a", 2), (Axis "c", 3)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "sizes isn't a subset of original axes" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start =
                  fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "d", 3)]
            let shape =
                  fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "d", 2)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "negative sizes" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start = fromKVPairs [(Axis "a", 1)]
            let shape = fromKVPairs [(Axis "a", -1)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "negative starts" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start = fromKVPairs [(Axis "a", -1)]
            let shape = fromKVPairs [(Axis "a", 1)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "starts+sizes >= original shape" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start = fromKVPairs [(Axis "a", 1)]
            let shape = fromKVPairs [(Axis "a", 5)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              },
          toTensorTest "slice sizes are zero" $ do
            let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
            let start =
                  fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)]
            let shape =
                  fromKVPairs [(Axis "a", 2), (Axis "b", 3), (Axis "c", 0)]
            TensorTest
              { tensor = dynamicSlice x $ DySliceArgs start shape,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
        ],
      testGroup "dynamicUpdateSlice" $ do
        let x = simpleTensor @SymInteger "x" [("a", 5), ("b", 6), ("c", 7)]
        let y = simpleTensor @SymInteger "y" [("a", 2), ("b", 3), ("c", 2)]
        let start = fromKVPairs [(Axis "a", 1), (Axis "b", 2), (Axis "c", 3)]
        let updated = dynamicUpdateSlice x y start
        let shape = fromKVPairs [(Axis "a", 5), (Axis "b", 6), (Axis "c", 7)]
        [ toTensorTest "access in slice" $ do
            TensorTest
              { tensor = updated,
                shape =
                  Just $
                    fromKVPairs [(Axis "a", 5), (Axis "b", 6), (Axis "c", 7)],
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 4), (Axis "c", 4)],
                expected = Just $ TensorElemVal "ya1b2c1"
              },
          toTensorTest "access in slice lower boundary" $ do
            TensorTest
              { tensor = updated,
                shape = Just shape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 4), (Axis "c", 3)],
                expected = Just $ TensorElemVal "ya1b2c0"
              },
          toTensorTest "access out of slice (smaller than)" $ do
            TensorTest
              { tensor = updated,
                shape = Just shape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 4), (Axis "c", 2)],
                expected = Just $ TensorElemVal "xa2b4c2"
              },
          toTensorTest "access out of slice (greater than)" $ do
            TensorTest
              { tensor = updated,
                shape = Just shape,
                access =
                  Just $
                    fromKVPairs [(Axis "a", 2), (Axis "b", 4), (Axis "c", 5)],
                expected = Just $ TensorElemVal "xa2b4c5"
              },
          toTensorTest "update sizes are zero" $ do
            let newUpdate = simpleTensor @SymInteger "y" [("a", 2), ("b", 3), ("c", 0)]
            TensorTest
              { tensor = dynamicUpdateSlice x newUpdate start,
                shape = Nothing,
                access = Nothing,
                expected = Nothing
              }
          ],
      testGroup
        "convBase"
        [ toTensorTest "2dconv, strided" $ do
            let x =
                  simpleTensor @TensorInt
                    "x"
                    [("b", 3), ("f", 4), ("s0", 5), ("s1", 6)]
            let y =
                  simpleTensor @TensorInt
                    "y"
                    [("o", 6), ("f", 4), ("s0", 2), ("s1", 4)]
            let batchAxes = HS.fromList [Axis "b"]
            let featureAxes = HS.fromList [Axis "f"]
            let outputFeatureAxes = HS.fromList [Axis "o"]
            let strides =
                  fromKVPairs [(Axis "s0", 1), (Axis "s1", 2)] :: Indices
            let sif = "sif"
            let sis0 = "sis0"
            let sis1 = "sis1"
            let si =
                  fromKVPairs
                    [(Axis "f", sif), (Axis "s0", sis0), (Axis "s1", sis1)] ::
                    Indices
            TensorTest
              { tensor =
                  convBase x y $
                    ConvConfigArgs
                      { convBatchAxes = batchAxes,
                        convFeatureAxes = featureAxes,
                        convOutputFeatureAxes = outputFeatureAxes,
                        convStrides = strides,
                        convContractingSIMap = si
                      },
                shape =
                  Just $
                    fromKVPairs
                      [ (Axis "b", 3),
                        (Axis "o", 6),
                        (Axis "s0", 4),
                        (Axis "s1", 2)
                      ],
                access =
                  Just $
                    fromKVPairs
                      [ (Axis "b", 2),
                        (Axis "o", 3),
                        (Axis "s0", 3),
                        (Axis "s1", 1)
                      ],
                expected =
                  let entry f s0 s1 =
                        ( sif .== con f .&& sis0 .== con s0 .&& sis1 .== con s1,
                          fromString
                            ( "xb2f"
                                <> show f
                                <> "s0"
                                <> show (s0 + 3)
                                <> "s1"
                                <> show (s1 + 1 * 2)
                            )
                            * fromString
                              ( "yo3f"
                                  <> show f
                                  <> "s0"
                                  <> show s0
                                  <> "s1"
                                  <> show s1
                              ) ::
                            TensorInt
                        )
                      table =
                        [ entry f s0 s1
                        | f <- [0 .. 3],
                          s0 <- [0 .. 1],
                          s1 <- [0 .. 3]
                        ]
                      res =
                        foldr
                          (\(c, v) acc -> symIte c v acc)
                          (snd $ last table)
                          (init table)
                   in Just $ TensorElemSum res
              }
        ]
    ]
