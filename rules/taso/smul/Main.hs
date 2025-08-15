module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (smul)

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

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02