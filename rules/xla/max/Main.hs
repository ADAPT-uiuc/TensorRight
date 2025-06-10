module Main (main) where

import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tNInf <- constant @a (negInf :: a) [rclass --> map]
  lhs <- numBinOp Max tA tNInf
  let rhs = tA
  rewrite "Max(A, -inf) ⇒ A" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tInf <- constant @a (posInf :: a) [rclass --> map]
  lhs <- numBinOp Min tA tInf
  let rhs = tA
  rewrite "Min(A, inf) ⇒ A" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
