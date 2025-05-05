module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValGe)

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  [rcSizeX, rcSizeYZ, rcStart] <- newMaps ["rcSizeX", "rcSizeY", "rcStart"] rclass
  tX <- newTensor @a "X" [rclass --> rcSizeX]
  tY <- newTensor @a "Y" [rclass --> rcSizeYZ]
  tZ <- newTensor @a "Z" [rclass --> rcSizeYZ]
  lhs <- numBinOp Add (dynamicUpdateSlice tX tY [rclass --> rcStart]) (dynamicUpdateSlice tX tZ [rclass --> rcStart])
  rhs <- dynamicUpdateSlice tX (numBinOp Add tY tZ) [rclass --> rcStart]
  rewrite "Add(DynamicUpdateSlice(X, Y, I), DynamicUpdateSlice(X, Z, I)) ==> DynamicUpdateSlice(X, Add(Y, Z), I)" lhs rhs

rule02 :: DSLContext Rewrite
rule02 = do
  -- TODO: Generalize to reals and other scalars
  rclass <- newRClass "rclass"
  [size, low, high, interior] <- newMaps ["size", "low", "high", "interior"] rclass
  tX <- newTensor @TensorInt "X" [rclass --> size]
  let padConfig =
        Padding
          { low = [rclass --> low],
            interior = [rclass --> interior],
            high = [rclass --> high]
          }
  lhs <- numBinScalarOp Mul (pad tX (3 :: TensorInt) padConfig) (2 :: TensorInt)
  rhs <- pad (numBinScalarOp Mul tX (2 :: TensorInt)) (6 :: TensorInt) padConfig
  rewrite "Mul(Pad(X, a, L, H, I), b) ==> Pad(Mul(X, b), a * b, L, H, I)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0Length] <- newMaps ["rc0Size", "rc0Start", "rc0Length"] rclass0
  [rc1Size, rc1SiL, rc1SiR] <- newMaps ["rc1Size", "rc1SiL", "rc1SiR"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  let dynamicSliceConfig =
        DySlice
          { start = [rclass0 --> rc0Start],
            sizes = [rclass0 --> rc0Length]
          }
  lhs <- dynamicSlice (reduce tX [rclass1 --> rc1SiL]) dynamicSliceConfig
  rhs <- reduce (dynamicSlice tX dynamicSliceConfig) [rclass1 --> rc1SiR]
  siRelation [rc1SiL, rc1SiR] $ \[rc1SiL, rc1SiR] -> rc1SiL .== rc1SiR
  checkSIMap [rc1SiL] [rc1SiR]
  rewrite "DynamicSlice(Reduce(add, X, dims), I, S) ==> Reduce(add, DynamicSlice(X, I, S), dims)" lhs rhs

rule05_slice :: forall a. NumRule a
rule05_slice _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <- newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1SiL, rc1SiR] <- newMaps ["rc1Size", "rc1SiL", "rc1SiR"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  let sliceConfig =
        Slice
          { start = [rclass0 --> rc0Start],
            end = [rclass0 --> rc0End],
            strides = [rclass0 --> rc0Stride]
          }
  lhs <- slice (reduce tX [rclass1 --> rc1SiL]) sliceConfig
  rhs <- reduce (slice tX sliceConfig) [rclass1 --> rc1SiR]
  siRelation [rc1SiL, rc1SiR] $ \[rc1SiL, rc1SiR] -> rc1SiL .== rc1SiR
  checkSIMap [rc1SiL] [rc1SiR]
  rewrite "Slice(Reduce(add, X, dims) ==> Reduce(add, Slice(X, S, E, P), dims), S, E, P)" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  zero <- constant @a 0 [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tX]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Max tX zero
  let rhs = tX
  rewrite "Max(X, 0) ==> X if NonNegative(X)" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  zero <- constant @a 0 [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tX]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Min tX zero
  let rhs = zero
  rewrite "Min(X, 0) ==> 0 if NonNegative(X)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyDSL rule02
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule05_slice ##############################"
  verifyNumDSL rule05_slice
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule07 ##############################"
  verifyNumDSL rule07
