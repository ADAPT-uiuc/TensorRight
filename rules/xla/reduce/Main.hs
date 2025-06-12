module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0LhsSi, rc0RhsSi] <-
    newMaps ["rclass0size", "rc0LhsSi", "rc0RhsSi"] rclass0
  [rc1Size, rc1LhsSi, rc1RhsSi] <-
    newMaps ["rclass1size", "rc1LhsSi", "rc1RhsSi"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size]
  tY <- newTensor @a "Y" [rclass1 --> rc1Size]
  lhs <-
    numBinOp
      Mul
      (reduce tX [rclass0 --> rc0LhsSi])
      (reduce tY [rclass1 --> rc1LhsSi])
  rhs <-
    reduce
      ( numBinOp
          Mul
          (broadcast tX [rclass1 --> rc1Size])
          (broadcast tY [rclass0 --> rc0Size])
      )
      [rclass0 --> rc0RhsSi, rclass1 --> rc1RhsSi]
  siRelation [rc0LhsSi, rc0RhsSi] $
    \[l, r] -> l .== r
  siRelation [rc1LhsSi, rc1RhsSi] $
    \[l, r] -> l .== r
  checkSIMap [rc0LhsSi, rc1LhsSi] [rc0RhsSi, rc1RhsSi]
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
  tX <- newTensor @a "X" [concatRClass --> concatSize0, otherRClass --> otherSize]
  tY <- newTensor @a "Y" [concatRClass --> concatSize1, otherRClass --> otherSize]
  lhs <-
    reduce
      ( concatTensor
          ( broadcast
              (reduce tX [concatRClass --> lhsSIInnerX])
              [concatRClass --> singletonConcat]
          )
          ( broadcast
              (reduce tY [concatRClass --> lhsSIInnerY])
              [concatRClass --> singletonConcat]
          )
          (ByRClass concatRClass)
      )
      [concatRClass --> lhsSIOuter]
  rhs <- reduce (concatTensor tX tY (ByRClass concatRClass)) [concatRClass --> rhsSI]
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
  rewrite "Reduce(Concat(Reduce(X), Reduce(Y))) ⇒ Reduce(Concat(X,Y))" lhs rhs

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
  [rc0Size, rc0LhsSi, rc0RhsSi] <-
    newMaps ["rc0Size", "rc0LhsSi", "rc0RhsSi"] rclass0
  [rc1Size, rc1LhsSi, rc1RhsSi] <-
    newMaps ["rc1Size", "rc1LhsSi", "rc1RhsSi"] rclass1
  rc2Size <- newMap "rc2Size" rclass2
  tX <-
    newTensor @a
      "X"
      [rclass0 --> rc0Size, rclass1 --> rc1Size, rclass2 --> rc2Size]
  lhs <- reduce (reduce tX [rclass0 --> rc0LhsSi]) [rclass1 --> rc1LhsSi]
  rhs <- reduce tX [rclass0 --> rc0RhsSi, rclass1 --> rc1RhsSi]
  siRelation [rc0LhsSi, rc0RhsSi] $
    \[l, r] -> l .== r
  siRelation [rc1LhsSi, rc1RhsSi] $
    \[l, r] -> l .== r
  checkSIMap [rc0LhsSi, rc1LhsSi] [rc0RhsSi, rc1RhsSi]
  rewrite "Reduce(Reduce(X)) ⇒ Reduce(X)" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  [rclass0, rclass1, rclass2, rclass3] <- newRClasses ["rclass0", "rclass1", "rclass2", "rclass3"]
  [rc0Size, rc0LhsSi, rc0RhsSi] <-
    newMaps ["rc0Size", "rc0LhsSi", "rc0RhsSi"] rclass0
  [rc1Size, rc1LhsSi, rc1RhsSi] <-
    newMaps ["rc1Size", "rc1LhsSi", "rc1RhsSi"] rclass1
  rc2Size <- newMap "rc2Size" rclass2
  rc3Size <- newMap "rc3Size" rclass3
  x <-
    newTensor @a
      "x"
      [rclass0 --> rc0Size, rclass1 --> rc1Size, rclass2 --> rc2Size]
  y <-
    newTensor @a
      "y"
      [rclass0 --> rc0Size, rclass1 --> rc1Size, rclass3 --> rc3Size]
  lhs <-
    reduce
      (dot x y [rclass0 --> rc0LhsSi] [ByRClass rclass1])
      [rclass1 --> rc1LhsSi]
  rhs <- dot x y [rclass0 --> rc0RhsSi, rclass1 --> rc1RhsSi] []
  siRelation [rc0LhsSi, rc0RhsSi] $
    \[l, r] -> l .== r
  siRelation [rc1LhsSi, rc1RhsSi] $
    \[l, r] -> l .== r
  checkSIMap [rc0LhsSi, rc1LhsSi] [rc0RhsSi, rc1RhsSi]
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
