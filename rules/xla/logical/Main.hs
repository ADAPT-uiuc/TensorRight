module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: DSLContext Rewrite
rule01 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp Or tensor (constant @SymBool (con True) [rclass --> map])
  rhs <- constant @SymBool (con True) [rclass --> map]
  rewrite "Or(A,True) ⇒ True" lhs rhs

rule02 :: DSLContext Rewrite
rule02 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp Or (constant @SymBool (con True) [rclass --> map]) tensor
  rhs <- constant @SymBool (con True) [rclass --> map]
  rewrite "Or(True,A) ⇒ True" lhs rhs

rule03 :: DSLContext Rewrite
rule03 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp Or tensor (constant @SymBool (con False) [rclass --> map])
  let rhs = tensor
  rewrite "Or(A,False) ⇒ A" lhs rhs

rule04 :: DSLContext Rewrite
rule04 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp Or (constant @SymBool (con False) [rclass --> map]) tensor
  let rhs = tensor
  rewrite "Or(False,A) ⇒ A" lhs rhs

rule05 :: DSLContext Rewrite
rule05 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp And tensor (constant @SymBool (con True) [rclass --> map])
  let rhs = tensor
  rewrite "And(A,1) ⇒ A" lhs rhs

rule06 :: DSLContext Rewrite
rule06 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp And (constant @SymBool (con True) [rclass --> map]) tensor
  let rhs = tensor
  rewrite "And(1,A) ⇒ A" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp And tensor (constant @SymBool (con False) [rclass --> map])
  rhs <- constant @SymBool (con False) [rclass --> map]
  rewrite "And(A,0) ⇒ 0" lhs rhs

rule08 :: DSLContext Rewrite
rule08 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @SymBool "tensor" [rclass --> map]
  lhs <- boolBinOp And (constant @SymBool (con False) [rclass --> map]) tensor
  rhs <- constant @SymBool (con False) [rclass --> map]
  rewrite "And(0,A) ⇒ 0" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor1 <- constant @a "a" [rclass --> map]
  constTensor2 <- constant @a "b" [rclass --> map]
  lhs <- boolBinOp And (compareOp Lt tensor constTensor1) (compareOp Gt constTensor2 tensor)
  rhs <- compareOp Lt tensor (numBinOp Min constTensor1 constTensor2)
  rewrite "And(A < Const, Const1 > A) ⇒ Lt(A, min(Const, Const1))" lhs rhs

rule10 :: forall a. NumRule a
rule10 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  t1 <- newTensor @a "t1" [rclass --> map]
  t2 <- newTensor @a "t2" [rclass --> map]
  lhs <- compareOp Gt (numBinOp Max t1 t2) t2
  rhs <- compareOp Gt t1 t2
  rewrite "Gt(Max(A,B),B) ⇒ Gt(A,B)" lhs rhs

rule11 :: forall a. NumRule a
rule11 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  t1 <- newTensor @a "t1" [rclass --> map]
  t2 <- newTensor @a "t2" [rclass --> map]
  lhs <- compareOp Gt (numBinOp Max t1 t2) t1
  rhs <- compareOp Gt t2 t1
  rewrite "Gt(Max(A,B),A) ⇒ Gt(B,A)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyDSL rule01
  print "############################## rule02 ##############################"
  verifyDSL rule02
  print "############################## rule03 ##############################"
  verifyDSL rule03
  print "############################## rule04 ##############################"
  verifyDSL rule04
  print "############################## rule05 ##############################"
  verifyDSL rule05
  print "############################## rule06 ##############################"
  verifyDSL rule06
  print "############################## rule07 ##############################"
  verifyDSL rule07
  print "############################## rule08 ##############################"
  verifyDSL rule08
  print "############################## rule09 ##############################"
  verifyNumDSL rule09
  print "############################## rule10 ##############################"
  verifyNumDSL rule10
  print "############################## rule11 ##############################"
  verifyNumDSL rule11
