module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (relu)

desugar :: forall a. NumRule a
desugar _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  input <- newTensor @a "input" [rclass --> size]
  lhs <- relu @a input
  rhs <- clampScalar @a 0 input posInf
  rewrite "TASO ReLU ⇒ Clamp(0, _, +∞)" lhs rhs

main :: IO ()
main = verifyNumDSL desugar
