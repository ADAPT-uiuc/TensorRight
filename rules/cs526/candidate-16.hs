module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValGe, tensorValLt)

rule02_v1 :: DSLContext Rewrite
rule02_v1 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Start, rc0End, rc0Strides] <- newMaps ["rc0Size", "rc0Start", "rc0End", "rc0Strides"] rclass0
  [rc1Size, rc1Start, rc1End, rc1Strides] <- newMaps ["rc1Size", "rc1Start", "rc1End", "rc1Strides"] rclass1
  precondition [rc0Strides] $ \[p] -> p .== 1
  precondition [rc0Start] $ \[s] -> s .== 0
  let rc0NewSize = rc0End
  rc1NewSize <- combineMap "rc1NewSize" (\[s, e, p] -> divOr 0 (e - s + p - 1) p) [rc1Start, rc1End, rc1Strides]
  let sliceConfig =
        Slice
          { start = [rclass0 --> rc0Start, rclass1 --> rc1Start],
            end = [rclass0 --> rc0End, rclass1 --> rc1End],
            strides = [rclass0 --> rc0Strides, rclass1 --> rc1Strides]
          }
  lhs <- slice (iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)) sliceConfig
  rhs <- iota [rclass0 --> rc0NewSize, rclass1 --> rc1NewSize] (ByRClass rclass0)
  rewrite "Slice(Iota(...)) ==> Iota(...)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [ta]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Max tX (numBinOp Min tY ta)
  rhs <- numBinOp Min (numBinOp Max tX ta) tY
  rewrite "Max(X, Min(Y, a)) ==> Min(Max(X, a), Y) if a >= 0" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [ta]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Max (numBinOp Min tX ta) tY
  rhs <- numBinOp Min (numBinOp Max tX tY) ta
  rewrite "Max(Min(X, a), Y) ==> Min(Max(X, Y), a) if a >= 0" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  lhs <- numBinOp Min (numBinOp Max ta tX) tY
  rhs <- numBinOp Min (numBinOp Max tX tY) ta
  rewrite "Min(Max(a, X), Y) ==> Min(Max(X, Y), a)" lhs rhs

rule08 :: forall a. NumRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  tb <- newTensor @a "b" [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tb]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Max ta (numBinOp Min tX tb)
  rhs <- numBinOp Min (numBinOp Max ta tX) tb
  rewrite "Max(a, Min(X, b)) ==> Min(Max(a, X), b) if b >= 0" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tb <- newTensor @a "b" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tb]
    forallIdx
    ( \[x] -> simpleMerge $ do
        u <- runExceptT $ tensorValGe x 0
        case u of
          Left _ -> con True
          Right v -> return v
    )
  lhs <- numBinOp Max (numBinOp Min tX tb) ta
  rhs <- numBinOp Min (numBinOp Max tX ta) tb
  rewrite "Max(Min(X, b), a) ==> Min(Max(X, a), b)" lhs rhs

rule10 :: forall a. NumRule a
rule10 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  ta <- newTensor @a "a" [rclass --> map]
  tb <- newTensor @a "b" [rclass --> map]
  lhs <- numBinOp Mul tX (clamp ta tY tb)
  rhs <- clamp (numBinOp Mul ta tX) (numBinOp Mul tX tY) (numBinOp Mul tb tX)
  rewrite "Mul(X, Clamp(a, Y, b)) ==> Clamp(Mul(a, X), Mul(X, Y), Mul(b, X))" lhs rhs

rule11 :: forall a. NumRule a
rule11 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  pred1 <- newTensor @SymBool "pred1" [rclass --> map]
  pred2 <- newTensor @SymBool "pred2" [rclass --> map]
  lhs <- numBinOp Add (select pred1 tX tY) (select pred2 tX tY)
  rhs <- select (boolBinOp Or pred1 pred2) tX tY
  rewrite "Add(Select(P, X, Y), Select(Q, X, Y)) ==> Select(Or(P, Q), X, Y)" lhs rhs

rule12 :: forall a. NumRule a
rule12 _ = do
  [rcX, rcYZ, rcContract] <- newRClasses ["rcX", "rcYZ", "rcContract"]
  sizeX <- newMap "sizeX" rcX
  sizeYZ <- newMap "sizeYZ" rcYZ
  sizeContract <- newMap "sizeContract" rcContract
  [siLXY, siLXZ, siR] <- newMaps ["siLXY", "siLXZ", "siR"] rcContract
  tX <- newTensor @a "X" [rcX --> sizeX, rcContract --> sizeContract]
  tY <- newTensor @a "Y" [rcYZ --> sizeYZ, rcContract --> sizeContract]
  tZ <- newTensor @a "Z" [rcYZ --> sizeYZ, rcContract --> sizeContract]
  lhs <- numBinOp Add (dot tX tY [rcContract --> siLXY] []) (dot tX tZ [rcContract --> siLXZ] [])
  rhs <- dot tX (numBinOp Add tY tZ) [rcContract --> siR] []
  siRelation [siLXY, siLXZ, siR] $ \[xy, xz, r] -> xy .== xz .&& xy .== r
  checkSIMap [siLXY, siLXZ] [siR]
  rewrite "Add(Dot(X, Y, C, PHI), Dot(X, Z, C, PHI)) ==> Dot(X, Add(Y, Z), C, PHI)" lhs rhs

main :: IO ()
main = do
  print "############################## rule02_v1 ##############################"
  verifyDSL rule02_v1
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule07 ##############################"
  verifyNumDSL rule07
  print "############################## rule08 ##############################"
  verifyNumDSL rule08
  print "############################## rule09 ##############################"
  verifyNumDSL rule09
  print "############################## rule10 ##############################"
  verifyNumDSL rule10
  print "############################## rule11 ##############################"
  verifyNumDSL rule11
  print "############################## rule12 ##############################"
  verifyNumDSL rule12
