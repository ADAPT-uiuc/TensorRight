module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rclass0size, rclass0exsize, rclass0lhssi, rclass0rhssi] <-
    newMaps ["rclass0size", "rclass0exsize", "rclass0lhssi", "rclass0rhssi"] rclass0
  [rclass1size, rclass1exsize, rclass1lhssi, rclass1rhssi] <-
    newMaps ["rclass1size", "rclass1exsize", "rclass1lhssi", "rclass1rhssi"] rclass1
  tensor0 <- newTensor @a "tensor0" [rclass0 --> rclass0size]
  tensor1 <- newTensor @a "tensor1" [rclass1 --> rclass1size]
  lhs <-
    numBinOp
      Mul
      (reduce tensor0 [rclass0 --> rclass0lhssi])
      (reduce tensor1 [rclass1 --> rclass1lhssi])
  rhs <-
    reduce
      ( numBinOp
          Mul
          (broadcast tensor0 [rclass1 --> rclass1exsize])
          (broadcast tensor1 [rclass0 --> rclass0exsize])
      )
      [rclass0 --> rclass0rhssi, rclass1 --> rclass1rhssi]
  precondition [rclass0size, rclass0exsize] $
    \[rclass0size, rclass0exsize] -> rclass0size .== rclass0exsize
  precondition [rclass1size, rclass1exsize] $
    \[rclass1size, rclass1exsize] -> rclass1size .== rclass1exsize
  siRelation [rclass0lhssi, rclass0rhssi] $
    \[rclass0lhssi, rclass0rhssi] -> rclass0lhssi .== rclass0rhssi
  siRelation [rclass1lhssi, rclass1rhssi] $
    \[rclass1lhssi, rclass1rhssi] -> rclass1lhssi .== rclass1rhssi
  checkSIMap [rclass0lhssi, rclass1lhssi] [rclass0rhssi, rclass1rhssi]
  rewrite
    "Mul(Reduce(X), Reduce(Y)) ⇒ Reduce(Mul(Broadcast(X), Broadcast(Y)))"
    lhs
    rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  [concatRClass, otherRClass] <- newRClasses ["concatRClass", "otherRClass"]
  [concatSize0, concatSize1] <-
    newMaps ["concatSize0", "concatSize1"] concatRClass
  singletonConcat <- newConstMap "singletonConcat" 1 concatRClass
  [otherSize] <- newMaps ["otherSize"] otherRClass
  [lhsSIInnerX, lhsSIInnerY, lhsSIOuter, rhsSI] <-
    newMaps ["lhsSIInnerX", "lhsSIInnerY", "lhsSIOuter", "rhsSI"] concatRClass
  x <- newTensor @a "x" [concatRClass --> concatSize0, otherRClass --> otherSize]
  y <- newTensor @a "y" [concatRClass --> concatSize1, otherRClass --> otherSize]
  lhs <-
    reduce
      ( concatTensor
          ( broadcast
              (reduce x [concatRClass --> lhsSIInnerX])
              [concatRClass --> singletonConcat]
          )
          ( broadcast
              (reduce y [concatRClass --> lhsSIInnerY])
              [concatRClass --> singletonConcat]
          )
          (ByRClass concatRClass)
      )
      [concatRClass --> lhsSIOuter]
  rhs <- reduce (concatTensor x y (ByRClass concatRClass)) [concatRClass --> rhsSI]
  monitorMapOnFailure "concatSize0" (ByRClass concatRClass) concatSize0
  monitorMapOnFailure "concatSize1" (ByRClass concatRClass) concatSize1
  monitorMapOnFailure "lhsSIInnerX" (ByRClass concatRClass) lhsSIInnerX
  monitorMapOnFailure "lhsSIInnerY" (ByRClass concatRClass) lhsSIInnerY
  monitorMapOnFailure "lhsSIOuter" (ByRClass concatRClass) lhsSIOuter

  siRelation [lhsSIInnerX, lhsSIInnerY, lhsSIOuter, rhsSI, concatSize0, concatSize1] $
    \[lhsSIInnerX, lhsSIInnerY, lhsSIOuter, rhsSI, concatSize0, concatSize1] ->
      (lhsSIInnerX .>= 0 .&& lhsSIInnerX .< concatSize0)
        .&& (lhsSIInnerY .>= 0 .&& lhsSIInnerY .< concatSize1)
        .&& (lhsSIOuter .== 0 .|| lhsSIOuter .== 1)
        .&& symIte
          (lhsSIOuter .== 0)
          (lhsSIInnerX .== rhsSI)
          (concatSize0 + lhsSIInnerY .== rhsSI)
  checkSIMap [lhsSIInnerX, lhsSIInnerY, lhsSIOuter] [rhsSI]
  rewrite "Reduce(Concat(Reduce(X),Reduce(Y))) ⇒ Reduce(Concat(X,Y))" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  [reductionRClass, rclass1] <- newRClasses ["reductionRClass", "rclass1"]
  [reductionSize] <- newMaps ["reductionSize"] reductionRClass
  [lhsSI, rhsSI] <- newMaps ["lhsSI", "rhsSI"] reductionRClass
  [otherSize] <- newMaps ["otherSize"] rclass1
  x <- newTensor @a "x" [reductionRClass --> reductionSize, rclass1 --> otherSize]
  lhs <-
    numBinOp
      Mul
      (constant @a "a" [rclass1 --> otherSize])
      (reduce x [reductionRClass --> lhsSI])
  rhs <-
    reduce
      ( numBinOp
          Mul
          ( constant @a
              "a"
              [reductionRClass --> reductionSize, rclass1 --> otherSize]
          )
          x
      )
      [reductionRClass --> rhsSI]
  siRelation [lhsSI, rhsSI] $ \[lhsSI, rhsSI] -> lhsSI .== rhsSI
  checkSIMap [lhsSI] [rhsSI]
  rewrite "Const * Reduce(X) ⇒ Reduce(Const * X)" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  [reductionRClass, nonReductionRClass] <- newRClasses ["reductionRClass", "nonReductionRClass"]
  [reductionSize] <-
    newMaps ["reductionSize"] reductionRClass
  [otherSize] <-
    newMaps ["otherSize"] nonReductionRClass
  [lhsSI, rhsSI] <- newMaps ["lhsSI", "rhsSI"] reductionRClass
  x <-
    newTensor @a
      "x"
      [ reductionRClass --> reductionSize @@ "l0",
        nonReductionRClass --> otherSize @@ "l1"
      ]
  lhs <-
    reduce
      ( relabel
          x
          [ ByLabel "l0" --> ByLabel "l1",
            ByLabel "l1" --> ByLabel "l0"
          ]
      )
      [ByLabel "l1" --> lhsSI]
  rhs <-
    relabel
      (reduce x [ByLabel "l0" --> rhsSI])
      [ByLabel "l1" --> ByLabel "l0"]
  siRelation [lhsSI, rhsSI] $ \[lhsSI, rhsSI] -> lhsSI .== rhsSI
  checkSIMap [lhsSI] [rhsSI]
  rewrite "Reduce(Relabel(X)) ⇒ Relabel(Reduce(X))" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  [rclass0, rclass1, rclass2] <- newRClasses ["rclass0", "rclass1", "rclass2"]
  [rclass0size, rclass0lsi, rclass0rsi] <-
    newMaps ["rclass0size", "rclass0lsi", "rclass0rsi"] rclass0
  [rclass1size, rclass1lsi, rclass1rsi] <-
    newMaps ["rclass1size", "rclass1lsi", "rclass1rsi"] rclass1
  rclass2size <- newMap "rclass2size" rclass2
  x <-
    newTensor @a
      "x"
      [rclass0 --> rclass0size, rclass1 --> rclass1size, rclass2 --> rclass2size]
  lhs <- reduce (reduce x [rclass0 --> rclass0lsi]) [rclass1 --> rclass1lsi]
  rhs <- reduce x [rclass0 --> rclass0rsi, rclass1 --> rclass1rsi]
  siRelation [rclass0lsi, rclass0rsi] $
    \[rclass0lsi, rclass0rsi] -> rclass0lsi .== rclass0rsi
  siRelation [rclass1lsi, rclass1rsi] $
    \[rclass1lsi, rclass1rsi] -> rclass1lsi .== rclass1rsi
  checkSIMap [rclass0lsi, rclass1lsi] [rclass0rsi, rclass1rsi]
  rewrite "Reduce(Reduce(X)) ⇒ Reduce(X)" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  [rclass0, rclass1, rclass2, rclass3] <- newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  [rclass0size, rclass0lsi, rclass0rsi] <-
    newMaps ["rclass0size", "rclass0lsi", "rclass0rsi"] rclass0
  [rclass1size, rclass1lsi, rclass1rsi] <-
    newMaps ["rclass1size", "rclass1lsi", "rclass1rsi"] rclass1
  rclass2size <- newMap "rclass2size" rclass2
  rclass3size <- newMap "rclass3size" rclass3
  x <-
    newTensor @a
      "x"
      [rclass0 --> rclass0size, rclass1 --> rclass1size, rclass2 --> rclass2size]
  y <-
    newTensor @a
      "y"
      [rclass0 --> rclass0size, rclass1 --> rclass1size, rclass3 --> rclass3size]
  lhs <-
    reduce
      (dot x y [rclass0 --> rclass0lsi] [ByRClass rclass1])
      [rclass1 --> rclass1lsi]
  rhs <- dot x y [rclass0 --> rclass0rsi, rclass1 --> rclass1rsi] []
  siRelation [rclass0lsi, rclass0rsi] $
    \[rclass0lsi, rclass0rsi] -> rclass0lsi .== rclass0rsi
  siRelation [rclass1lsi, rclass1rsi] $
    \[rclass1lsi, rclass1rsi] -> rclass1lsi .== rclass1rsi
  checkSIMap [rclass0lsi, rclass1lsi] [rclass0rsi, rclass1rsi]
  rewrite "Reduce(Dot(X,Y)) ⇒ Dot(X,Y)" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  [rclassDegenerate, rclass1] <- newRClasses ["rclassDegenerate", "rclass1"]
  rclassDegenerateSize <- newConstMap "rclassDegenerateSize" 1 rclassDegenerate
  rclass1Size <- newMap "rclass1Size" rclass1
  x <- newTensor @a "x" [rclassDegenerate --> rclassDegenerateSize, rclass1 --> rclass1Size]
  siDegenerate <- newMap "siDegenerate" rclassDegenerate

  lhs <- reduce x [rclassDegenerate --> siDegenerate]
  rhs <- reshapeDegenerate x [] [ByRClass rclassDegenerate]

  siRelation [siDegenerate] $ \[siDegenerate] -> siDegenerate .== 0
  checkSIMap [siDegenerate] []
  rewrite "Reduce(X) ⇒ ReshapeDegenerate(X)" lhs rhs

rule08 :: forall a. NumRule a
rule08 _ = do
  [rclassDegenerate, rclass1] <- newRClasses ["rclassDegenerate", "rclass1"]
  rclassDegenerateSize <- newConstMap "rclassDegenerateSize" 1 rclassDegenerate
  rclass1Size <- newMap "rclass1Size" rclass1
  x <- newTensor @a "x" [rclassDegenerate --> rclassDegenerateSize, rclass1 --> rclass1Size]
  siDegenerate <- newMap "siDegenerate" rclassDegenerate

  lhs <-
    reduce
      (relabel x [rclassDegenerate --> ByLabel "l0"])
      [ByLabel "l0" --> siDegenerate]
  rhs <- reshapeDegenerate x [] [ByRClass rclassDegenerate]

  siRelation [siDegenerate] $ \[siDegenerate] -> siDegenerate .== 0
  checkSIMap [siDegenerate] []
  rewrite "Reduce(X) ⇒ ReshapeDegenerate(X)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule07 ##############################"
  verifyNumDSL rule07
  print "############################## rule08 ##############################"
  verifyNumDSL rule08
