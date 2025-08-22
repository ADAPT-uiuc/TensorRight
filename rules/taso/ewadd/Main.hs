module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd)

rule01 :: forall a. NumRule a -- Verify desugaring
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- ewadd tA tB
  rhs <- numBinOp Add tA tB
  rewrite "ewadd(A, B) ⇒ Add(A, B)" lhs rhs

rule02 :: forall a. NumRule a -- Associativity
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "t" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewadd x $ ewadd y z
  rhs <- ewadd (ewadd x y) z
  rewrite "ewadd(x, ewadd(y, z)) ⇒ Add(ewadd(x, y), z)" lhs rhs

rule03 :: forall a. NumRule a -- Verify commutative
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- ewadd x y
  rhs <- ewadd y x
  rewrite "ewadd(x, y) ⇒ ewadd(y, x)" lhs rhs

main :: IO ()
main = do
  printTitle "############################## rule01 ##############################"
  verifyNumDSL rule01
  printTitle "############################## rule02 ##############################"
  verifyNumDSL rule02
  printTitle "############################## rule03 ##############################"
  verifyNumDSL rule03