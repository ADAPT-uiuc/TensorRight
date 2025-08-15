module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd, ewmul, smul)

rule01 :: forall a. NumRule a -- Verify desugaring
rule01 _ = do
  let s = ("s" :: a)
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- smul tA s
  rhs <- numBinScalarOp Mul tA s
  rewrite "smul(A, s) ⇒ Mul(A, s)" lhs rhs

rule02 :: forall a. NumRule a -- Verify associativity
rule02 _ = do
  let w = ("w" :: a)
  let y = ("y" :: a)
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  lhs <- smul (smul x y) w
  rhs <- smul x (y * w) -- Multiply the scalars first since smul (y, w) doesn't make sense
  rewrite "smul(smul(x, y), w) ⇒ smul(x, smul(y, w))" lhs rhs

rule03 :: forall a. NumRule a -- Distributivity
rule03 _ = do
  let w = ("w" :: a)
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- smul (ewadd x y) w
  rhs <- ewadd (smul x w) (smul y w)
  rewrite "smul(ewadd(x, y), w) ⇒ ewadd(smul(x, w), smul(y, w))" lhs rhs

rule04 :: forall a. NumRule a -- Operator commutativity
rule04 _ = do
  let w = ("w" :: a)
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  x <- newTensor @a "x" [rclass --> map]
  y <- newTensor @a "y" [rclass --> map]
  lhs <- smul (ewmul x y) w
  rhs <- ewmul x (smul y w)
  rewrite "smul(ewmul(x, y), w) ⇒ ewmul(x, smul(y, w))" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04