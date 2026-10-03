module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (ewadd)

desugar :: forall a. NumRule a
desugar _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  lhsInput <- newTensor @a "lhs" [rclass --> size]
  rhsInput <- newTensor @a "rhs" [rclass --> size]
  lhs <- ewadd lhsInput rhsInput
  rhs <- numBinOp Add lhsInput rhsInput
  rewrite "TASO EwAdd ⇒ Add" lhs rhs

associativity :: forall a. NumRule a
associativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  z <- newTensor @a "z" [rclass --> size]
  yz <- ewadd y z
  lhs <- ewadd x yz
  xy <- ewadd x y
  rhs <- ewadd xy z
  rewrite "TASO EwAdd associativity" lhs rhs

commutativity :: forall a. NumRule a
commutativity _ = do
  rclass <- newRClass "rclass"
  size <- newMap "size" rclass
  x <- newTensor @a "x" [rclass --> size]
  y <- newTensor @a "y" [rclass --> size]
  lhs <- ewadd x y
  rhs <- ewadd y x
  rewrite "TASO EwAdd commutativity" lhs rhs

main :: IO ()
main = verifyNumDSL desugar >> verifyNumDSL associativity >> verifyNumDSL commutativity
