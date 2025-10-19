module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (newRClass)
import TensorRight.Internal.DSL.TASO (ewadd, ewmul)

desugar :: forall a. NumRule a -- Verify desugaring
desugar _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- ewmul tA tB
  rhs <- numBinOp Mul tA tB
  rewrite "ewmul(A, B) ⇒ Mul(A, B)" lhs rhs

associativity :: forall a. NumRule a -- Associativity
associativity _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "t" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewmul x $ ewmul y z
  rhs <- ewmul (ewmul x y) z
  rewrite "ewmul(x, ewmul(y, z)) ⇒ mul(ewmul(x, y), z)" lhs rhs

commutativity :: forall a. NumRule a -- Verify commutative
commutativity _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- ewmul x y
  rhs <- ewmul y x
  rewrite "ewmul(x, y) ⇒ ewmul(y, x)" lhs rhs

distributivity :: forall a. NumRule a -- Verify distributivity
distributivity _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewmul (ewadd x y) z
  rhs <- ewadd (ewmul x z) (ewmul y z)
  rewrite "ewmul(ewadd(x, y), z) ⇒ ewadd(ewmul(x, z), ewmul(y, z))" lhs rhs

identity :: forall a. NumRule a -- Verify identity
identity _ = do
  rclassN <- newRClass "rclassN"
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassN --> sizeN]
  ones <- constant @a 1 [rclassN --> sizeN]

  lhs <- ewmul x ones
  let rhs = x

  rewrite "ewmul(x, I) ⇒ x" lhs rhs

main :: IO ()
main = do
  printTitle "############################## desugar ##############################"
  verifyNumDSL desugar
  printTitle "############################## associativity ##############################"
  verifyNumDSL associativity
  printTitle "############################## commutativity ##############################"
  verifyNumDSL commutativity
  printTitle "############################## distributivity ##############################"
  verifyNumDSL distributivity
  printTitle "############################## identity ##############################"
  verifyNumDSL identity