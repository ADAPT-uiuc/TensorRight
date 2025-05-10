module Main (main) where

import Control.Monad.Except (runExceptT)
import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.Core.Tensor.TensorInt (tensorValLe)

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [xs0, ys0, dotsi, sixc, siyd, sir, rclass0AllOne] <-
    newMaps
      ["xs0", "ys0", "dotsi", "sixc", "siyd", "sir", "allOne"]
      rclass0
  [xs1, ys1] <- newMaps ["xs1", "ys1"] rclass1
  [cs2, ds2] <- newMaps ["cs2", "ds2"] rclass2
  x <- newTensor @a "x" [rclass0 --> xs0, rclass1 --> xs1]
  y <- newTensor @a "y" [rclass0 --> ys0, rclass1 --> ys1]
  c <- newTensor @a "c" [rclass0 --> xs0, rclass2 --> cs2]
  d <- newTensor @a "d" [rclass0 --> ys0, rclass2 --> ds2]
  lhs <-
    dot
      (concatTensor x y $ ByRClass rclass0)
      (concatTensor c d $ ByRClass rclass0)
      [rclass0 --> dotsi]
      []
  rhs <-
    reduce
      ( concatTensor
          (broadcast (dot x c [rclass0 --> sixc] []) [rclass0 --> rclass0AllOne])
          (broadcast (dot y d [rclass0 --> siyd] []) [rclass0 --> rclass0AllOne])
          $ ByRClass rclass0
      )
      [rclass0 --> sir]
  precondition [rclass0AllOne] $ \[rclass0AllOne] -> rclass0AllOne .== 1
  let siCondition [vdotsi, vsixc, vsiyd, vsir, vxs0, vys0] =
        symIte
          (vsir .== 0)
          (vdotsi .== vsixc)
          (vdotsi .== vsiyd + vxs0)
          .&& (vsixc .>= 0)
          .&& (vsiyd .>= 0)
          .&& (vsixc .< vxs0)
          .&& (vsiyd .< vys0)
          .&& (vsir .== 0 .|| vsir .== 1)
      siCondition _ = undefined
  siRelation [dotsi, sixc, siyd, sir, xs0, ys0] siCondition
  checkSIMap [dotsi] [sir, sixc, siyd]
  let lhsStr = "Dot(Concat(X, Y), Concat(C, D))"
  let rhsStr = "Reduce(Concat(Broadcast(Dot(X, C)), Broadcast(Dot(Y, D)))"
  rewrite (lhsStr <> " ⇒ " <> rhsStr) lhs rhs

rule02_forward :: forall a. NumRule a
rule02_forward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0sizeXY, rc0sizeUV] <- newMaps ["rc0sizeX", "rc0sizeUV"] rclass0
  rc1size <- newMap "rc1size" rclass1
  zeroMap <- newConstMap "zeroMap" 0 rclass0
  oneMap <- newConstMap "oneMap" 1 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tY <- newTensor @a "Y" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tU <- newTensor @a "U" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  tV <- newTensor @a "V" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  lhs <- concatTensor (numBinOp Mul tX tY) (numBinOp Mul tU tV) (ByRClass rclass0)
  rhs <- numBinOp Mul (concatTensor tX tU (ByRClass rclass0)) (concatTensor tY tV (ByRClass rclass0))
  rewrite "Concat(Mul(X, Y), Mul(U, V), dim) ==> Mul(Concat(X, U, dim), Concat(Y, V, dim))" lhs rhs

rule02_backward :: forall a. NumRule a
rule02_backward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0sizeXY, rc0sizeUV] <- newMaps ["rc0sizeX", "rc0sizeUV"] rclass0
  rc1size <- newMap "rc1size" rclass1
  zeroMap <- newConstMap "zeroMap" 0 rclass0
  oneMap <- newConstMap "oneMap" 1 rclass0
  tX <- newTensor @a "X" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tY <- newTensor @a "Y" [rclass0 --> rc0sizeXY, rclass1 --> rc1size]
  tU <- newTensor @a "U" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  tV <- newTensor @a "V" [rclass0 --> rc0sizeUV, rclass1 --> rc1size]
  lhs <- numBinOp Mul (concatTensor tX tU (ByRClass rclass0)) (concatTensor tY tV (ByRClass rclass0))
  rhs <- concatTensor (numBinOp Mul tX tY) (numBinOp Mul tU tV) (ByRClass rclass0)
  rewrite "Mul(Concat(X, U, dim), Concat(Y, V, dim)) ==> Concat(Mul(X, Y), Mul(U, V), dim)" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tMinO <- newTensor @a "MinO" [rclass --> map]
  tMaxO <- newTensor @a "MaxO" [rclass --> map]
  tMinI <- newTensor @a "MinI" [rclass --> map]
  tMaxI <- newTensor @a "MaxI" [rclass --> map]
  lhs <- clamp tMinO (clamp tMinI tX tMaxI) tMaxO
  rhs <- clamp tMinO tX tMaxO
  rewrite "Clamp(MinO, Clamp(MinI, X, MaxI), MaxO) ⇒ Clamp(MinO, X, MaxO)" lhs rhs

rule03_v1 :: forall a. NumRule a
rule03_v1 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tMinO <- newTensor @a "MinO" [rclass --> map]
  tMaxO <- newTensor @a "MaxO" [rclass --> map]
  tMinI <- newTensor @a "MinI" [rclass --> map]
  tMaxI <- newTensor @a "MaxI" [rclass --> map]
  lhs <- clamp tMinO (clamp tMinI tX tMaxI) tMaxO
  rhs <- clamp tMinO tX tMaxO
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tMinI, tMinO]
    forallIdx
    ( \[minI, minO] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe minI minO
        case u of
          Left _ -> con True
          Right v -> return v
    )
  numTensorAssumption
    [tMaxO, tMaxI]
    forallIdx
    ( \[maxO, maxI] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe maxO maxI
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Clamp(MinO, Clamp(MinI, X, MaxI), MaxO) ⇒ Clamp(MinO, X, MaxO) if minI <= minO and maxO <= maxI" lhs rhs

rule03_v2 :: forall a. NumRule a
rule03_v2 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tMinO <- newTensor @a "MinO" [rclass --> map]
  tMaxO <- newTensor @a "MaxO" [rclass --> map]
  tMinI <- newTensor @a "MinI" [rclass --> map]
  tMaxI <- newTensor @a "MaxI" [rclass --> map]
  lhs <- clamp tMinO (clamp tMinI tX tMaxI) tMaxO
  rhs <- clamp tMinI tX tMaxI
  rewrite "Clamp(MinO, Clamp(MinI, X, MaxI), MaxO) ⇒ Clamp(MinI, X, MaxI)" lhs rhs

rule03_v3 :: forall a. NumRule a
rule03_v3 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tMinO <- newTensor @a "MinO" [rclass --> map]
  tMaxO <- newTensor @a "MaxO" [rclass --> map]
  tMinI <- newTensor @a "MinI" [rclass --> map]
  tMaxI <- newTensor @a "MaxI" [rclass --> map]
  lhs <- clamp tMinO (clamp tMinI tX tMaxI) tMaxO
  rhs <- clamp tMinI tX tMaxI
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tMinO, tMinI]
    forallIdx
    ( \[minO, minI] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe minO minI
        case u of
          Left _ -> con True
          Right v -> return v
    )
  numTensorAssumption
    [tMaxI, tMaxO]
    forallIdx
    ( \[maxI, maxO] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe maxI maxO
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Clamp(MinO, Clamp(MinI, X, MaxI), MaxO) ⇒ Clamp(MinI, X, MaxI) if minO <= minI and maxI <= maxO" lhs rhs

rule03_v4 :: forall a. NumRule a
rule03_v4 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tMinO <- newTensor @a "MinO" [rclass --> map]
  tMaxO <- newTensor @a "MaxO" [rclass --> map]
  tMinI <- newTensor @a "MinI" [rclass --> map]
  tMaxI <- newTensor @a "MaxI" [rclass --> map]
  lhs <- clamp tMinO (clamp tMinI tX tMaxI) tMaxO
  rhs <- clamp tMinI tX tMaxI
  forallIdx <- newMap "forallIdx" rclass
  numTensorAssumption
    [tMinO, tMinI]
    forallIdx
    ( \[minO, minI] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe minO minI
        case u of
          Left _ -> con True
          Right v -> return v
    )
  numTensorAssumption
    [tMaxI, tMaxO]
    forallIdx
    ( \[maxI, maxO] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe maxI maxO
        case u of
          Left _ -> con True
          Right v -> return v
    )
  numTensorAssumption
    [tMinI, tMaxI]
    forallIdx
    ( \[minI, maxI] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe minI maxI
        case u of
          Left _ -> con True
          Right v -> return v
    )
  numTensorAssumption
    [tMinO, tMaxO]
    forallIdx
    ( \[minO, maxO] -> simpleMerge $ do
        u <- runExceptT $ tensorValLe minO maxO
        case u of
          Left _ -> con True
          Right v -> return v
    )
  rewrite "Clamp(MinO, Clamp(MinI, X, MaxI), MaxO) ⇒ Clamp(MinI, X, MaxI) if [minI, maxI] in [minO, maxO]" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tMin <- newTensor @a "Min" [rclass --> map]
  tMax <- newTensor @a "Max" [rclass --> map]
  lhs <- clamp tMin (numBinOp Mul tX tY) tMax
  rhs <- numBinOp Mul (clamp tMin tX tMax) (clamp tMin tY tMax)
  rewrite "Clamp(Min, Mul(X, Y), Max) ⇒ Mul(Clamp(Min, X, Max), Clamp(Min, Y, Max))" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tMin <- newTensor @a "Min" [rclass --> map]
  tMax <- newTensor @a "Max" [rclass --> map]
  lhs <- clamp tMin (numBinOp Sub tX tY) tMax
  rhs <- numBinOp Sub (clamp tMin tX tMax) (clamp tMin tY tMax)
  rewrite "Clamp(Min, Sub(X, Y), Max) ⇒ Sub(Clamp(Min, X, Max), Clamp(Min, Y, Max))" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numBinOp Add (numUnaryOp Neg tX) (numUnaryOp Neg tY)
  rhs <- numUnaryOp Neg (numBinOp Add tX tY)
  rewrite "Add(Neg(X), Neg(Y)) ⇒ Neg(Add(X, Y))" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  lhs <- numUnaryOp Neg (numBinOp Sub tX tY)
  rhs <- numBinOp Sub tY tX
  rewrite "Neg(Sub(X, Y)) ⇒ Sub(Y, X)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02_forward ##############################"
  verifyNumDSL rule02_forward
  print "############################## rule02_backward ##############################"
  verifyNumDSL rule02_backward
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule03_v1 ##############################"
  verifyNumDSL rule03_v1
  print "############################## rule03_v2 ##############################"
  verifyNumDSL rule03_v2
  print "############################## rule03_v3 ##############################"
  verifyNumDSL rule03_v3
  print "############################## rule03_v4 ##############################"
  verifyNumDSL rule03_v4
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule07 ##############################"
  verifyNumDSL rule07
