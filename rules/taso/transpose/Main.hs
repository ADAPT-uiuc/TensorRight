module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (newSingletonRClass, twoRefsOf)
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, relu, smul, transpose)
import Prelude hiding (concat)

-- ############################# (Rewrite rules not enforcing singleton) ############################
-- Desugaring for general TASO transpose
desugarTranspose :: forall a. AnyDTypeRule a
desugarTranspose _ = do
  rclass <- newSingletonRClass "rclass"
  s1 <- newMap "s1" rclass
  s2 <- newMap "s2" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  lhs <- transpose tA
  (a, b) <- twoRefsOf tA
  rhs <- relabel tA [ByLabel "L" --> ByLabel "R", ByLabel "R" --> ByLabel "L"]
  rewrite "transpose(A) ⇒ relabel(A, swap)" lhs rhs

inverse :: forall a. AnyDTypeRule a
inverse _ = do
  rclass <- newSingletonRClass "rclass"
  s1 <- newMap "s1" rclass
  s2 <- newMap "s2" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  lhs <- transpose $ transpose tA
  rewrite "transpose(transpose(A)) ⇒ A" lhs tA

-- transpose(ewadd(x, y)) = ewadd(transpose(x), transpose(y))
transposeEwadd :: forall a. NumRule a
transposeEwadd _ = do
  r <- newSingletonRClass "r"
  sL <- newMap "sL" r
  sR <- newMap "sR" r
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  y <- newTensor @a "y" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transpose (ewadd x y)
  rhs <- ewadd (transpose x) (transpose y)
  rewrite "transpose(ewadd(x,y)) ⇒ ewadd(transpose(x), transpose(y))" lhs rhs

-- transpose(ewmul(x, y)) = ewmul(transpose(x), transpose(y))
transposeEwmul :: forall a. NumRule a
transposeEwmul _ = do
  r <- newSingletonRClass "r"
  sL <- newMap "sL" r
  sR <- newMap "sR" r
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  y <- newTensor @a "y" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transpose (ewmul x y)
  rhs <- ewmul (transpose x) (transpose y)
  rewrite "transpose(ewmul(x,y)) ⇒ ewmul(transpose(x), transpose(y))" lhs rhs

-- transpose(smul(x, w)) = smul(transpose(x), w)
transposeSmul :: forall a. NumRule a
transposeSmul _ = do
  r <- newSingletonRClass "r"
  sL <- newMap "sL" r
  sR <- newMap "sR" r
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  let w = ("w" :: a)
  lhs <- transpose (smul x w)
  rhs <- smul (transpose x) w
  rewrite "transpose(smul(x,w)) ⇒ smul(transpose(x), w)" lhs rhs

-- transpose(relu(x)) = relu(transpose(x))
transposeRelu :: forall a. NumRule a
transposeRelu _ = do
  r <- newSingletonRClass "r"
  sL <- newMap "sL" r
  sR <- newMap "sR" r
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transpose (relu @a x)
  rhs <- relu @a (transpose x)
  rewrite "transpose(relu(x)) ⇒ relu(transpose(x))" lhs rhs

-- concat(1, transpose(x), transpose(y)) = transpose(concat(0, x, y))
transposeConcat :: forall a. AnyDTypeRule a
transposeConcat _ = do
  -- Use same rclass with two labels for 2D
  r <- newSingletonRClass "r"
  sLx <- newMap "sLx" r
  sRx <- newMap "sRx" r
  sLy <- newMap "sLy" r
  sRy <- newMap "sRy" r
  x <- newTensor @a "x" [r --> sLx @@ "L", r --> sRx @@ "R"]
  y <- newTensor @a "y" [r --> sLy @@ "L", r --> sRy @@ "R"]
  -- concat along label "R" (axis 1), then transpose should move concat to axis 0 (label "L")
  let axis1 = ByLabel "R"
  let axis0 = ByLabel "L"
  lhs <- concat axis1 (transpose x) (transpose y)
  rhs <- transpose (concat axis0 x y)
  rewrite "concat(1, transpose(x), transpose(y)) ⇒ transpose(concat(0, x, y))" lhs rhs

main :: IO ()
main = do
  printTitle "######################## desugarTranspose ########################"
  verifyNumDSL desugarTranspose
  printTitle "######################## inverse #################################"
  verifyNumDSL inverse
  printTitle "######################## transposeEwadd ##########################"
  verifyNumDSL transposeEwadd
  printTitle "######################## transposeEwmul ##########################"
  verifyNumDSL transposeEwmul
  printTitle "######################## transposeSmul ###########################"
  verifyNumDSL transposeSmul
  printTitle "######################## transposeRelu ###########################"
  verifyNumDSL transposeRelu
  printTitle "######################## transposeConcat #########################"
  verifyNumDSL transposeConcat
