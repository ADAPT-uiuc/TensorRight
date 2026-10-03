module Main (main) where

import Data.Text (Text)
import TensorRight
import TensorRight.Internal.Core.Tensor (ToDType)
import TensorRight.Internal.DSL.DSL (Expr)
import TensorRight.Internal.DSL.Identifier (RClassIdentifier)
import TensorRight.Internal.DSL.Shape (RClassRef (ByLabel))
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, relu, smul, transpose)
import Prelude hiding (concat)

newMatrix :: forall a. (ToDType a) => Text -> DSLContext (Expr, RClassIdentifier, RClassRef, RClassRef)
newMatrix name = do
  axes <- newRClass $ name <> "-axes"
  rows <- newMap (name <> "-rows") axes
  columns <- newMap (name <> "-columns") axes
  let row = ByLabel $ name <> "-row"
      column = ByLabel $ name <> "-column"
  tensor <- newTensor @a name [axes --> rows @@ (name <> "-row"), axes --> columns @@ (name <> "-column")]
  pure (tensor, axes, row, column)

desugar :: forall a. NumRule a
desugar _ = do
  (input, _, row, column) <- newMatrix @a "input"
  lhs <- transpose input
  rhs <- relabel input [row --> column, column --> row]
  rewrite "TASO transpose ⇒ rank-two axis swap" lhs rhs

inverse :: forall a. NumRule a
inverse _ = do
  (input, _, _, _) <- newMatrix @a "input"
  lhs <- transpose =<< transpose input
  rewrite "TASO transpose is involutive" lhs input

commuteEwAdd :: forall a. NumRule a
commuteEwAdd _ = do
  (x, axes, row, column) <- newMatrix @a "x"
  rows <- newMap "y-rows" axes
  columns <- newMap "y-columns" axes
  y <- newTensor @a "y" [axes --> rows @@ "x-row", axes --> columns @@ "x-column"]
  lhs <- transpose =<< ewadd x y
  transposedX <- transpose x
  transposedY <- transpose y
  rhs <- ewadd transposedX transposedY
  rewrite "TASO transpose commutes with ewadd" lhs rhs

commuteEwMul :: forall a. NumRule a
commuteEwMul _ = do
  (x, axes, row, column) <- newMatrix @a "x"
  rows <- newMap "y-rows" axes
  columns <- newMap "y-columns" axes
  y <- newTensor @a "y" [axes --> rows @@ "x-row", axes --> columns @@ "x-column"]
  lhs <- transpose =<< ewmul x y
  transposedX <- transpose x
  transposedY <- transpose y
  rhs <- ewmul transposedX transposedY
  rewrite "TASO transpose commutes with ewmul" lhs rhs

commuteScalarMultiply :: forall a. NumRule a
commuteScalarMultiply _ = do
  (input, _, _, _) <- newMatrix @a "input"
  let scalar = ("scalar" :: a)
  transposed <- transpose input
  lhs <- smul transposed scalar
  rhs <- transpose =<< smul input scalar
  rewrite "TASO transpose commutes with scalar multiplication" lhs rhs

commuteRelu :: forall a. NumRule a
commuteRelu _ = do
  (input, _, _, _) <- newMatrix @a "input"
  lhs <- transpose =<< relu @a input
  rhs <- relu @a =<< transpose input
  rewrite "TASO transpose commutes with relu" lhs rhs

commuteConcat :: forall a. NumRule a
commuteConcat _ = do
  (x, axes, row, column) <- newMatrix @a "x"
  yRows <- newMap "y-rows" axes
  yColumns <- newMap "y-columns" axes
  y <- newTensor @a "y" [axes --> yRows @@ "x-row", axes --> yColumns @@ "x-column"]
  lhs <- transpose =<< concat row x y
  transposedX <- transpose x
  transposedY <- transpose y
  rhs <- concat column transposedX transposedY
  rewrite "TASO transpose moves concat from axis zero to axis one" lhs rhs

main :: IO ()
main = do
  verifyNumDSL desugar
  verifyNumDSL inverse
  verifyNumDSL commuteEwAdd
  verifyNumDSL commuteEwMul
  verifyNumDSL commuteScalarMultiply
  verifyNumDSL commuteRelu
  verifyNumDSL commuteConcat
