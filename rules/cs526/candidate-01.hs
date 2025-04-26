module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  sizeMap0 <- newMap "sizeMap" rclass0
  sizeMap1 <- newMap "sizeMap" rclass1
  tP <- newTensor @SymBool "P" [rclass0 --> sizeMap0]
  tX <- newTensor @a "X" [rclass0 --> sizeMap0]
  tY <- newTensor @a "Y" [rclass0 --> sizeMap0]
  tP' <- broadcast tP [rclass1 --> sizeMap1]
  tX' <- broadcast tX [rclass1 --> sizeMap1]
  tY' <- broadcast tY [rclass1 --> sizeMap1]
  lhs <- select tP' tX' tY'
  rhs <- broadcast (select tP tX tY) [rclass1 --> sizeMap1]
  rewrite "Select(Broadcast(P, S), Broadcast(X, S), Broadcast(Y, S)) ==> Broadcast(Select(P, X, Y), S)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @a "X" [rclass --> sizeMap]
  tY <- newTensor @a "Y" [rclass --> sizeMap]
  lhs <- numBinOp Add tX (numBinOp Mul tX tY)
  rhs <- numBinOp Mul tX (numBinOp Add (constant @a 1 [rclass --> sizeMap]) tY)
  rewrite "Add(X, Mul(X, Y)) ==> Mul(X, Add(1, Y))" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @a "X" [rclass --> sizeMap]
  lhs <- numBinOp Add tX (numUnaryOp Neg tX)
  rhs <- constant @a 0 [rclass --> sizeMap]
  rewrite "Add(X, Neg(X)) ==> 0" lhs rhs

rule09 :: DSLContext Rewrite
rule09 = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @TensorReal "X" [rclass --> sizeMap]
  tY <- newTensor @TensorReal "Y" [rclass --> sizeMap]
  tZ <- newTensor @TensorReal "Z" [rclass --> sizeMap]
  lhs <- numBinOp Sub (numBinOp Div tX tY) (numBinOp Div tZ tY)
  rhs <- numBinOp Div (numBinOp Sub tX tZ) tY
  rewrite "Sub(Div(X, Y), Div(Z, Y)) ==> Div(Sub(X, Z), Y)" lhs rhs

main :: IO ()
main = do
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule09 ##############################"
  verifyDSL rule09
