module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: DSLContext Rewrite
rule01 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp Or tA (constant @SymBool (con True) [rclass --> map])
  rhs <- constant @SymBool (con True) [rclass --> map]
  rewrite "Or(A, True) ⇒ True" lhs rhs

rule02 :: DSLContext Rewrite
rule02 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp Or (constant @SymBool (con True) [rclass --> map]) tA
  rhs <- constant @SymBool (con True) [rclass --> map]
  rewrite "Or(True, A) ⇒ True" lhs rhs

rule03 :: DSLContext Rewrite
rule03 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp Or tA (constant @SymBool (con False) [rclass --> map])
  let rhs = tA
  rewrite "Or(A, False) ⇒ A" lhs rhs

rule04 :: DSLContext Rewrite
rule04 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp Or (constant @SymBool (con False) [rclass --> map]) tA
  let rhs = tA
  rewrite "Or(False, A) ⇒ A" lhs rhs

rule05 :: DSLContext Rewrite
rule05 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp And tA (constant @SymBool (con True) [rclass --> map])
  let rhs = tA
  rewrite "And(A, 1) ⇒ A" lhs rhs

rule06 :: DSLContext Rewrite
rule06 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp And (constant @SymBool (con True) [rclass --> map]) tA
  let rhs = tA
  rewrite "And(1, A) ⇒ A" lhs rhs

rule07 :: DSLContext Rewrite
rule07 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp And tA (constant @SymBool (con False) [rclass --> map])
  rhs <- constant @SymBool (con False) [rclass --> map]
  rewrite "And(A, 0) ⇒ 0" lhs rhs

rule08 :: DSLContext Rewrite
rule08 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolBinOp And (constant @SymBool (con False) [rclass --> map]) tA
  rhs <- constant @SymBool (con False) [rclass --> map]
  rewrite "And(0, A) ⇒ 0" lhs rhs

rule09 :: forall a. NumRule a
rule09 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  constTensor1 <- constant @a "a" [rclass --> map]
  constTensor2 <- constant @a "b" [rclass --> map]
  lhs <- boolBinOp And (compareOp Lt tA constTensor1) (compareOp Gt constTensor2 tA)
  rhs <- compareOp Lt tA (numBinOp Min constTensor1 constTensor2)
  rewrite "And(A < Const, Const1 > A) ⇒ Lt(A, min(Const, Const1))" lhs rhs

rule10 :: forall a. NumRule a
rule10 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- compareOp Gt (numBinOp Max tA tB) tB
  rhs <- compareOp Gt tA tB
  rewrite "Gt(Max(A, B), B) ⇒ Gt(A, B)" lhs rhs

rule11 :: forall a. NumRule a
rule11 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- compareOp Gt (numBinOp Max tA tB) tA
  rhs <- compareOp Gt tB tA
  rewrite "Gt(Max(A, B), A) ⇒ Gt(B, A)" lhs rhs

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
