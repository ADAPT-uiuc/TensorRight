module Main (main) where

import Grisette (cvc5)
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 1 [rclass --> map]
  lhs <- numBinOp Mul tensor constTensor
  let rhs = tensor
  rewrite "Mul(A,1) ⇒ A" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 1 [rclass --> map]
  lhs <- numBinOp Mul constTensor tensor
  let rhs = tensor
  rewrite "Mul(1,A) ⇒ A" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Mul tensor constTensor
  let rhs = constTensor
  rewrite "Mul(A,0) ⇒ 0" lhs rhs

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Mul constTensor tensor
  let rhs = constTensor
  rewrite "Mul(0,A) ⇒ 0" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  t1 <- newTensor @a "t1" [rclass --> map]
  t2 <- newTensor @a "t2" [rclass --> map]
  constTensor1 <- constant @a "a" [rclass --> map]
  constTensor2 <- constant @a "b" [rclass --> map]
  lhs <- numBinOp Mul (numBinOp Mul t1 constTensor1) (numBinOp Mul t2 constTensor2)
  rhs <- numBinOp Mul (numBinOp Mul t1 t2) (numBinOp Mul constTensor1 constTensor2)
  rewrite "Mul(Mul(A, Const1), Mul(B, Const2)) ⇒ Mul(Mul(A, B),Mul(Const1,Const2))" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor1 <- constant @a "a" [rclass --> map]
  constTensor2 <- constant @a "b" [rclass --> map]
  lhs <- numBinOp Mul (numBinOp Mul tensor constTensor1) constTensor2
  rhs <- numBinOp Mul tensor (numBinOp Mul constTensor1 constTensor2)
  rewrite "Mul(Mul(A, Const1), Const2) ⇒ Mul(A, Mul(Const1,Const2))" lhs rhs

rule07 :: forall a. NumRule a
rule07 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  map0 <- newMap "map0" rclass0
  map1 <- newMap "map1" rclass1
  t1 <- newTensor @a "t1" [rclass0 --> map0, rclass1 --> map1]
  t2 <- newTensor @a "t2" [rclass0 --> map0]
  lhs <- numBinOp Mul (numBinOp Mul t1 (constant @a "a" [rclass0 --> map0, rclass1 --> map1])) (broadcast t2 [rclass1 --> map1])
  rhs <- numBinOp Mul (broadcast (numBinOp Mul t2 (constant @a "a" [rclass0 --> map0])) [rclass1 --> map1]) t1
  rewrite "Mul(Mul(A, Const1), Broadcast(B)) ⇒ Mul(Broadcast(Mul(B, Const1), A))" lhs rhs

rule08 :: forall a. NumRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  t1 <- newTensor @a "t1" [rclass --> map]
  t2 <- newTensor @a "t2" [rclass --> map]
  t3 <- newTensor @a "t3" [rclass --> map]
  lhs <- numBinOp Add (numBinOp Mul t1 t3) (numBinOp Mul t2 t3)
  rhs <- numBinOp Mul (numBinOp Add t1 t2) t3
  rewrite "Add(Mul(A,C),Mul(B,C)) ⇒ Mul(Add(A,B),C)" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  lhs <- numBinOp Mul (numUnaryOp Abs tensor) (numUnaryOp Abs tensor)
  rhs <- numBinOp Mul tensor tensor
  rewrite "Mul(Abs(A),Abs(A)) ⇒ Mul(A,A)" lhs rhs

rule10 :: DSLContext Rewrite
rule10 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  a <- newTensor @TensorReal "a" [rclass --> map]
  b <- newTensor @TensorReal "b" [rclass --> map]
  lhs <- numBinOp Mul (numUnaryOp Exp a) (numUnaryOp Exp b)
  rhs <- numUnaryOp Exp (numBinOp Add a b)
  rewrite "Mul(Exp(A),Exp(B)) ⇒ Exp(Add(A,B))" lhs rhs

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
