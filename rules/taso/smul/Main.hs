module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd, ewmul, smul)

desugar :: forall a. NumRule a
desugar _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  let scalar = "scalar" :: a
  lhs <- smul x scalar
  rhs <- numBinScalarOp Mul x scalar
  rewrite "TASO Smul ⇒ scalar Mul" lhs rhs

associativity :: forall a. NumRule a
associativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  let y = "y" :: a
      w = "w" :: a
  xy <- smul x y
  lhs <- smul xy w
  rhs <- smul x (y * w)
  rewrite "TASO Smul associativity" lhs rhs

distributivity :: forall a. NumRule a
distributivity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  let scalar = "scalar" :: a
  xy <- ewadd x y
  lhs <- smul xy scalar
  xs <- smul x scalar
  ys <- smul y scalar
  rhs <- ewadd xs ys
  rewrite "TASO Smul distributivity" lhs rhs

commutativity :: forall a. NumRule a
commutativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  let scalar = "scalar" :: a
  xy <- ewmul x y
  lhs <- smul xy scalar
  ys <- smul y scalar
  rhs <- ewmul x ys
  rewrite "TASO Smul/EwMul commutativity" lhs rhs

main :: IO ()
main = do
  verifyNumDSL desugar
  verifyNumDSL associativity
  verifyNumDSL distributivity
  verifyNumDSL commutativity
