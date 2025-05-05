module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValLt)

rule02 :: forall a. NumRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  [lSiX, lSiY, rSiXY] <- newMaps ["lSiX", "lSiY", "rSiXY"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tY <- newTensor @a "Y" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <-
    numBinOp
      Add
      (reduce tX [rclass1 --> lSiX])
      (reduce tY [rclass1 --> lSiY])
  rhs <- reduce (numBinOp Add tX tY) [rclass1 --> rSiXY]
  siRelation [lSiX, lSiY] $ \[lSiX, lSiY] -> lSiX .== lSiY
  siRelation [lSiX, rSiXY] $ \[lSiX, rSiXY] -> lSiX .== rSiXY
  checkSIMap [lSiX, lSiY] [rSiXY]
  rewrite "Add(Reduce(X, dims), Reduce(Y, dims)) ==> Reduce(Add(X, Y), dims)" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  rc2Size <- newMap "rc2Size" rclass2
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tY <- newTensor @a "Y" [rclass2 --> rc2Size]
  lhs <- reverseTensor (dot tX tY [] []) [ByRClass rclass1]
  rhs <- dot (reverseTensor tX [ByRClass rclass1]) tY [] []
  rewrite "Reverse(Dot(X, Y, PHI, PHI), dims) ==> Dot(Rev(X, dims), Y, PHI, PHI)" lhs rhs

rule04_v1 :: forall a. NumRule a
rule04_v1 _ = do
  [rclass0, rclass1, rclass2, rclass3] <- newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  rc2Size <- newMap "rc2Size" rclass2
  rc3Size <- newMap "rc3Size" rclass3
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tY <- newTensor @a "Y" [rclass2 --> rc2Size, rclass3 --> rc3Size]
  lhs <- reverseTensor (dot tX tY [] []) [ByRClass rclass1, ByRClass rclass3]
  rhs <- dot (reverseTensor tX [ByRClass rclass1]) (reverseTensor tY [ByRClass rclass3]) [] []
  rewrite "Rev(Dot(X, Y, PHI, PHI), dims) ==> Dot(Rev(X, dims1), Rev(Y, dims2), PHI, PHI)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- numBinOp Min tA (numBinOp Max tX tB)
  rhs <- numBinOp Min tX tA
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tA, tB]
    forallIdx
    ( \[c1, c2] -> simpleMerge $ do
        u <- runExceptT $ tensorValLt c1 c2
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Min(A, Max(X, B)) ==> Min(X, A) if A <= B" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @TensorReal "X" [rclass --> map]
  tY <- newTensor @TensorReal "Y" [rclass --> map]
  lhs <- numBinOp Max (numUnaryOp Exp tX) (numUnaryOp Exp tY)
  rhs <- numUnaryOp Exp (numBinOp Max tX tY)
  rewrite "Max(Exp(X), Exp(Y)) ==> Exp(Max(X, Y))" lhs rhs

rule08 :: DSLContext Rewrite
rule08 = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rc0Size <- newMap "rc0Size" rclass0
  [rc1SizeL, rc1SizeR] <- newMaps ["rc1SizeL", "rc1SizeR"] rclass1
  rc2Size <- newMap "rc2Size" rclass2
  iotaL <- iota [rclass0 --> rc0Size, rclass1 --> rc1SizeL, rclass2 --> rc2Size] (ByRClass rclass0)
  iotaR <- iota [rclass0 --> rc0Size, rclass1 --> rc1SizeR, rclass2 --> rc2Size] (ByRClass rclass0)
  lhs <- concatTensor iotaL iotaR (ByRClass rclass1)
  rc1SizeLR <- combineMap "rc1SizeL" sum [rc1SizeL, rc1SizeR]
  rhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1SizeLR, rclass2 --> rc2Size] (ByRClass rclass0)
  rewrite "Concat(Iota(S1, dim1), Iota(S2, dim1)) ==> Iota(S1 + S2, dim1)" lhs rhs

rule10 :: forall a. AnyDTypeRule a
rule10 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <- newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <- newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  let sliceConfig =
        Slice
          { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
            end = [rclass0 --> rc0End, rclass1 --> rc1End],
            strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
          }
  lhs <- reverseTensor (slice (reverseTensor tX [ByRClass rclass0]) sliceConfig) [ByRClass rclass0]
  rhs <- slice tX sliceConfig
  precondition [rc0Stride] $ \[p] -> p .== 1
  rewrite "Rev(Slice(Rev(X, dims), I_s, I_e, I_p), dims) ==> Slice(X, I_s, I_e, I_p) if I_p = 1" lhs rhs

rule10_v1 :: forall a. AnyDTypeRule a
rule10_v1 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Stride] <- newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Stride"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Stride] <- newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Stride"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  let sliceConfig =
        Slice
          { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
            end = [rclass0 --> rc0End, rclass1 --> rc1End],
            strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
          }
  lhs <- reverseTensor (slice (reverseTensor tX [ByRClass rclass0]) sliceConfig) [ByRClass rclass0]
  rc0NewStart <- combineMap "rc0NewStart" (\[d, e] -> d - e) [rc0Size, rc0End]
  rc0NewEnd <- combineMap "rc0NewEnd" (\[d, s] -> d - s) [rc0Size, rc0Start]
  let newSliceConfig =
        Slice
          { start = [rclass0 --> rc0NewStart, rclass1 --> rc1Start],
            end = [rclass0 --> rc0NewEnd, rclass1 --> rc1End],
            strides = [rclass0 --> rc0Stride, rclass1 --> rc1Stride]
          }
  rhs <- slice tX newSliceConfig
  precondition [rc0Stride] $ \[p] -> p .== 1
  rewrite "Rev(Slice(Rev(X, dims), I_s, I_e, I_p), dims) ==> Slice(X, I_s, I_e, I_p) if I_p = 1" lhs rhs

rule11 :: DSLContext Rewrite
rule11 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  shiftedIota <- numBinScalarOp Add (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) (1 :: TensorInt)
  rc0Zero <- newConstMap "rc0Zero" 0 rclass0
  rc0One <- newConstMap "rc0One" 1 rclass0
  rc1Zero <- newConstMap "rc1Zero" 0 rclass1
  lhs <- pad shiftedIota (0 :: TensorInt) $
    Padding
      { low = [rclass0 --> rc0One, rclass1 --> rc1Zero],
        interior = [rclass0 --> rc0Zero, rclass1 --> rc1Zero],
        high = [rclass0 --> rc0Zero, rclass1 --> rc1Zero]
      }
  rc0NewSize <- combineMap "rc0NewSize" (\[s] -> s + 1) [rc0Size]
  rhs <- iota [rclass0 --> rc0NewSize, rclass1 --> rc1Size] (ByRClass rclass0)
  rewrite "Pad(Iota(S, dim), 0, 1, 0, 0) ==> Iota(S+1, dim)" lhs rhs

rule12 :: DSLContext Rewrite
rule12 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  lhs <- reverseTensor (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) [ByRClass rclass0]
  rhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)
  rewrite "Rev(Iota(S, dim), dim) ==> Iota(S, dim)" lhs rhs

rule12_v1 :: DSLContext Rewrite
rule12_v1 = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  rc2Size <- newMap "rc2Size" rclass2
  lhs <- reverseTensor (iota [rclass0 --> rc0Size, rclass1 --> rc1Size, rclass2 --> rc2Size] (ByRClass rclass0)) [ByRClass rclass1]
  rhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1Size, rclass2 --> rc2Size] (ByRClass rclass0)
  rewrite "Rev(Iota(S, dim), dim1) ==> Iota(S, dim)" lhs rhs

main :: IO ()
main = do
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule04_v1 ##############################"
  verifyNumDSL rule04_v1
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule07 ##############################"
  verifyDSLWith cvc5 rule07
  print "############################## rule08 ##############################"
  verifyDSL rule08
  print "############################## rule10 ##############################"
  verifyAnyDTypeDSL rule10
  print "############################## rule10_v1 ##############################"
  verifyAnyDTypeDSL rule10_v1
  print "############################## rule11 ##############################"
  verifyDSL rule11
  print "############################## rule12 ##############################"
  verifyDSL rule12
  print "############################## rule12_v1 ##############################"
  verifyDSL rule12_v1
