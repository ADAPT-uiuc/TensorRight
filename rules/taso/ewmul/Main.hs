module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (newRClass)
import TensorRight.Internal.DSL.TASO (ewadd, ewmul)

rule01 :: forall a. NumRule a -- Verify desugaring
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- ewmul tA tB
  rhs <- numBinOp Mul tA tB
  rewrite "ewmul(A, B) ⇒ Mul(A, B)" lhs rhs

rule02 :: forall a. NumRule a -- Associativity
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "t" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewmul x $ ewmul y z
  rhs <- ewmul (ewmul x y) z
  rewrite "ewmul(x, ewmul(y, z)) ⇒ mul(ewmul(x, y), z)" lhs rhs

rule03 :: forall a. NumRule a -- Verify commutative
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- ewmul x y
  rhs <- ewmul y x
  rewrite "ewmul(x, y) ⇒ ewmul(y, x)" lhs rhs

rule04 :: forall a. NumRule a -- Verify distributivity
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  z <- newTensor @a "z" [rclass --> map]
  lhs <- ewmul (ewadd x y) z
  rhs <- ewadd (ewmul x z) (ewmul y z)
  rewrite "ewmul(ewadd(x, y), z) ⇒ ewadd(ewmul(x, z), ewmul(y, z))" lhs rhs

rule05 :: forall a. NumRule a -- Verify identity
rule05 _ = do
  rclassN <- newRClass "rclassN"
  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"]
  ones <- constant @a 1 [rclassN --> sizeN @@ "L", rclassN --> sizeN @@ "R"]

  lhs <- ewmul x ones
  let rhs = x

  rewrite "ewmul(x, I) ⇒ x" lhs rhs

main :: IO ()
main = do
  printTitle "############################## rule01 ##############################"
  verifyNumDSL rule01
  printTitle "############################## rule02 ##############################"
  verifyNumDSL rule02
  printTitle "############################## rule03 ##############################"
  verifyNumDSL rule03
  printTitle "############################## rule04 ##############################"
  verifyNumDSL rule04
  printTitle "############################## rule05 ##############################"
  verifyNumDSL rule05