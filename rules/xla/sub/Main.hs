module Main (main) where

import TensorRight

rule00 :: forall a. NumRule a
rule00 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Sub tensor constTensor
  let rhs = tensor
  rewrite "Sub(A,0) ⇒ A" lhs rhs

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a "x" [rclass --> map]
  negConstTensor <- constant @a (-"x") [rclass --> map]
  lhs <- numBinOp Sub tensor constTensor
  rhs <- numBinOp Add tensor negConstTensor
  rewrite "Sub(A,Const) ⇒ Add(A,Neg(Const))" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  constTensor <- constant @a 0 [rclass --> map]
  lhs <- numBinOp Sub tensor tensor
  let rhs = constTensor
  rewrite "Sub(A,A) ⇒ 0" lhs rhs

main :: IO ()
main = do
  print "############################## rule00 ##############################"
  verifyNumDSL rule00
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
