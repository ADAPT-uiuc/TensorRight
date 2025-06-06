module Main (main) where

import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  a <- newTensor @a "a" [rclass --> map]
  b <- constant @a (negInf :: a) [rclass --> map]
  lhs <- numBinOp Max a b
  let rhs = a
  rewrite "Max(A,-inf) ⇒ A" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  a <- newTensor @a "a" [rclass --> map]
  b <- constant @a (posInf :: a) [rclass --> map]
  lhs <- numBinOp Min a b
  let rhs = a
  rewrite "Min(A,inf) ⇒ A" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
