module Main (main) where

import TensorRight
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, relu, smul)
import Prelude hiding (concat)

desugar :: forall a. NumRule a
desugar _ = do
  rclass <- newRClass "rclass"
  lhsSize <- newMap "lhsSize" rclass
  rhsSize <- newMap "rhsSize" rclass
  lhsInput <- newTensor @a "lhs" [rclass --> lhsSize]
  rhsInput <- newTensor @a "rhs" [rclass --> rhsSize]
  let axis = ByRClass rclass
  lhs <- concat axis lhsInput rhsInput
  rhs <- concatTensor lhsInput rhsInput axis
  rewrite "TASO Concat ⇒ Concatenate" lhs rhs

commuteScalarMultiply :: forall a. NumRule a
commuteScalarMultiply _ = do
  rclass <- newRClass "rclass"
  lhsSize <- newMap "lhsSize" rclass
  rhsSize <- newMap "rhsSize" rclass
  x <- newTensor @a "x" [rclass --> lhsSize]
  y <- newTensor @a "y" [rclass --> rhsSize]
  let axis = ByRClass rclass
      scalar = ("scalar" :: a)
  lhsX <- smul x scalar
  lhsY <- smul y scalar
  lhs <- concat axis lhsX lhsY
  joined <- concat axis x y
  rhs <- smul joined scalar
  rewrite "TASO concat commutes with scalar multiplication" lhs rhs

commuteEwAdd :: forall a. NumRule a
commuteEwAdd _ = do
  rclass <- newRClass "rclass"
  lhsSize <- newMap "lhsSize" rclass
  rhsSize <- newMap "rhsSize" rclass
  x <- newTensor @a "x" [rclass --> lhsSize]
  y <- newTensor @a "y" [rclass --> lhsSize]
  z <- newTensor @a "z" [rclass --> rhsSize]
  w <- newTensor @a "w" [rclass --> rhsSize]
  let axis = ByRClass rclass
  lhsLeft <- ewadd x y
  lhsRight <- ewadd z w
  lhs <- concat axis lhsLeft lhsRight
  rhsLeft <- concat axis x z
  rhsRight <- concat axis y w
  rhs <- ewadd rhsLeft rhsRight
  rewrite "TASO concat commutes with ewadd" lhs rhs

commuteEwMul :: forall a. NumRule a
commuteEwMul _ = do
  rclass <- newRClass "rclass"
  lhsSize <- newMap "lhsSize" rclass
  rhsSize <- newMap "rhsSize" rclass
  x <- newTensor @a "x" [rclass --> lhsSize]
  y <- newTensor @a "y" [rclass --> lhsSize]
  z <- newTensor @a "z" [rclass --> rhsSize]
  w <- newTensor @a "w" [rclass --> rhsSize]
  let axis = ByRClass rclass
  lhsLeft <- ewmul x y
  lhsRight <- ewmul z w
  lhs <- concat axis lhsLeft lhsRight
  rhsLeft <- concat axis x z
  rhsRight <- concat axis y w
  rhs <- ewmul rhsLeft rhsRight
  rewrite "TASO concat commutes with ewmul" lhs rhs

commuteRelu :: forall a. NumRule a
commuteRelu _ = do
  rclass <- newRClass "rclass"
  lhsSize <- newMap "lhsSize" rclass
  rhsSize <- newMap "rhsSize" rclass
  x <- newTensor @a "x" [rclass --> lhsSize]
  y <- newTensor @a "y" [rclass --> rhsSize]
  let axis = ByRClass rclass
  lhsX <- relu @a x
  lhsY <- relu @a y
  lhs <- concat axis lhsX lhsY
  joined <- concat axis x y
  rhs <- relu @a joined
  rewrite "TASO concat commutes with relu" lhs rhs

geometry :: forall a. NumRule a
geometry _ = do
  [axis0, axis1] <- newRClasses ["axis0", "axis1"]
  axis0Size <- newMap "axis0Size" axis0
  axis1Size <- newMap "axis1Size" axis1
  x <- newTensor @a "x" [axis0 --> axis0Size, axis1 --> axis1Size]
  y <- newTensor @a "y" [axis0 --> axis0Size, axis1 --> axis1Size]
  z <- newTensor @a "z" [axis0 --> axis0Size, axis1 --> axis1Size]
  w <- newTensor @a "w" [axis0 --> axis0Size, axis1 --> axis1Size]
  let d0 = ByRClass axis0
      d1 = ByRClass axis1
  lhsXY <- concat d1 x y
  lhsZW <- concat d1 z w
  lhs <- concat d0 lhsXY lhsZW
  rhsXZ <- concat d0 x z
  rhsYW <- concat d0 y w
  rhs <- concat d1 rhsXZ rhsYW
  rewrite "TASO concat geometry" lhs rhs

main :: IO ()
main = do
  verifyNumDSL desugar
  verifyNumDSL commuteScalarMultiply
  verifyNumDSL commuteEwAdd
  verifyNumDSL commuteEwMul
  verifyNumDSL commuteRelu
  verifyNumDSL geometry
