module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (concat, split0, split1)
import Prelude hiding (concat)

split0Definition :: forall a. NumRule a
split0Definition _ = do
  [concatAxis, otherAxis] <- newRClasses ["concatAxis", "otherAxis"]
  lhsSize <- newMap "lhsSize" concatAxis
  rhsSize <- newMap "rhsSize" concatAxis
  otherSize <- newMap "otherSize" otherAxis
  x <- newTensor @a "x" [concatAxis --> lhsSize, otherAxis --> otherSize]
  y <- newTensor @a "y" [concatAxis --> rhsSize, otherAxis --> otherSize]
  let axis = ByRClass concatAxis
  joined <- concat axis x y
  lhs <- split0 axis joined
  rewrite "TASO split0(axis, concat(axis, x, y)) ⇒ x" lhs x

split1Definition :: forall a. NumRule a
split1Definition _ = do
  [concatAxis, otherAxis] <- newRClasses ["concatAxis", "otherAxis"]
  lhsSize <- newMap "lhsSize" concatAxis
  rhsSize <- newMap "rhsSize" concatAxis
  otherSize <- newMap "otherSize" otherAxis
  x <- newTensor @a "x" [concatAxis --> lhsSize, otherAxis --> otherSize]
  y <- newTensor @a "y" [concatAxis --> rhsSize, otherAxis --> otherSize]
  let axis = ByRClass concatAxis
  joined <- concat axis x y
  lhs <- split1 axis joined
  rewrite "TASO split1(axis, concat(axis, x, y)) ⇒ y" lhs y

main :: IO ()
main = verifyNumDSL split0Definition >> verifyNumDSL split1Definition
