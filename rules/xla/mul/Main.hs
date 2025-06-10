module Main (main) where

import Grisette (cvc5)
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  one <- constant @a 1 [rclass --> map]
  lhs <- numBinOp Mul tA one
  let rhs = tA
  rewrite "Mul(A, 1) ⇒ A" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  one <- constant @a 1 [rclass --> map]
  lhs <- numBinOp Mul one tA
  let rhs = tA
  rewrite "Mul(1, A) ⇒ A" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  zero <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Mul tA zero
  let rhs = zero
  rewrite "Mul(A, 0) ⇒ 0" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  zero <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Mul zero tensor
  let rhs = zero
  rewrite "Mul(0, A) ⇒ 0" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  c1 <- constant @a "c1" [rclass --> map]
  c2 <- constant @a "c2" [rclass --> map]
  lhs <- numBinOp Mul (numBinOp Mul tA c1) (numBinOp Mul tB c2)
  rhs <- numBinOp Mul (numBinOp Mul tA tB) (numBinOp Mul c1 c2)
  rewrite "Mul(Mul(A, Const1), Mul(B, Const2)) ⇒ Mul(Mul(A, B), Mul(Const1, Const2))" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  c1 <- constant @a "c1" [rclass --> map]
  c2 <- constant @a "c2" [rclass --> map]
  lhs <- numBinOp Mul (numBinOp Mul tA c1) c2
  rhs <- numBinOp Mul tA (numBinOp Mul c1 c2)
  rewrite "Mul(Mul(A, Const1), Const2) ⇒ Mul(A, Mul(Const1, Const2))" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1
  tA <- newTensor @a "A" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tB <- newTensor @a "B" [rclass0 --> rc0Size]
  lhs <- numBinOp Mul (numBinOp Mul tA (constant @a "a" [rclass0 --> rc0Size, rclass1 --> rc1Size])) (broadcast tB [rclass1 --> rc1Size])
  rhs <- numBinOp Mul (broadcast (numBinOp Mul tB (constant @a "a" [rclass0 --> rc0Size])) [rclass1 --> rc1Size]) tA
  rewrite "Mul(Mul(A, Const1), Broadcast(B)) ⇒ Mul(Broadcast(Mul(B, Const1), A))" lhs rhs

rule08 :: forall a. NumRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  tC <- newTensor @a "C" [rclass --> map]
  lhs <- numBinOp Add (numBinOp Mul tA tC) (numBinOp Mul tB tC)
  rhs <- numBinOp Mul (numBinOp Add tA tB) tC
  rewrite "Add(Mul(A, C), Mul(B, C)) ⇒ Mul(Add(A, B), C)" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- numBinOp Mul (numUnaryOp Abs tA) (numUnaryOp Abs tA)
  rhs <- numBinOp Mul tA tA
  rewrite "Mul(Abs(A), Abs(A)) ⇒ Mul(A, A)" lhs rhs

rule10 :: DSLContext Rewrite
rule10 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @TensorReal "A" [rclass --> map]
  tB <- newTensor @TensorReal "B" [rclass --> map]
  lhs <- numBinOp Mul (numUnaryOp Exp tA) (numUnaryOp Exp tB)
  rhs <- numUnaryOp Exp (numBinOp Add tA tB)
  rewrite "Mul(Exp(A), Exp(B)) ⇒ Exp(Add(A, B))" lhs rhs

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
  print "############################## rule09 ##############################"
  verifyNumDSL rule09
  print "############################## rule10 ##############################"
  verifyDSLWith cvc5 rule10
