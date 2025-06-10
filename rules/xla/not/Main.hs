module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: DSLContext Rewrite
rule01 = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @SymBool "A" [rclass --> map]
  lhs <- boolUnaryOp Not (boolUnaryOp Not tA)
  let rhs = tA
  rewrite "Not(Not(A)) ⇒ A" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- numUnaryOp Neg (numUnaryOp Neg tA)
  let rhs = tA
  rewrite "Negate(Negate(A)) ⇒ A" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
