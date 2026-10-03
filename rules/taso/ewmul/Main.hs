module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd, ewmul)

desugar :: forall a. NumRule a
desugar _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  lhsInput <- newTensor @a "lhs" [rclass --> size]
  rhsInput <- newTensor @a "rhs" [rclass --> size]
  lhs <- ewmul lhsInput rhsInput
  rhs <- numBinOp Mul lhsInput rhsInput
  rewrite "TASO EwMul ⇒ Mul" lhs rhs

associativity :: forall a. NumRule a
associativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  z <- newTensor @a "z" [rclass --> size]
  yz <- ewmul y z
  lhs <- ewmul x yz
  xy <- ewmul x y
  rhs <- ewmul xy z
  rewrite "TASO EwMul associativity" lhs rhs

commutativity :: forall a. NumRule a
commutativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  lhs <- ewmul x y
  rhs <- ewmul y x
  rewrite "TASO EwMul commutativity" lhs rhs

distributivity :: forall a. NumRule a
distributivity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  z <- newTensor @a "z" [rclass --> size]
  xy <- ewadd x y
  lhs <- ewmul xy z
  xz <- ewmul x z
  yz <- ewmul y z
  rhs <- ewadd xz yz
  rewrite "TASO EwMul distributivity" lhs rhs

identity :: forall a. NumRule a
identity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  ones <- constant @a 1 [rclass --> size]
  lhs <- ewmul x ones
  rewrite "TASO EwMul identity" lhs x

main :: IO ()
main = do
  verifyNumDSL desugar
  verifyNumDSL associativity
  verifyNumDSL commutativity
  verifyNumDSL distributivity
  verifyNumDSL identity
