module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd)

desugar :: forall a. NumRule a -- Verify desugaring
desugar _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- ewadd tA tB
  rhs <- numBinOp Add tA tB
  rewrite "ewadd(A, B) ⇒ Add(A, B)" lhs rhs

associativity :: forall a. NumRule a -- Associativity
associativity _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewadd x $ ewadd y z
  rhs <- ewadd (ewadd x y) z
  rewrite "ewadd(x, ewadd(y, z)) ⇒ Add(ewadd(x, y), z)" lhs rhs

commutativity :: forall a. NumRule a -- Verify commutative
commutativity _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- ewadd x y
  rhs <- ewadd y x
  rewrite "ewadd(x, y) ⇒ ewadd(y, x)" lhs rhs

main :: IO ()
main = do
  printTitle "############################## desugar ##############################"
  verifyNumDSL desugar
  printTitle "############################## associativity ##############################"
  verifyNumDSL associativity
  printTitle "############################## commutativity ##############################"
  verifyNumDSL commutativity
