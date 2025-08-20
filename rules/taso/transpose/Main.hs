module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (transpose2DSingleton, twoRefsOf, twoSingletonRefsOf)
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, relu, smul, transpose, transposeSingleton)
import Prelude hiding (concat)

-- ############################# (Rewrite rules not enforcing singleton) ############################
-- Desugaring for general TASO transpose
desugarTranspose :: forall a. AnyDTypeRule a
desugarTranspose _ = do
  rclass <- newRClass "rclass"
  s1 <- newMap "s1" rclass
  s2 <- newMap "s2" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  lhs <- transpose tA
  (a, b) <- twoRefsOf tA
  rhs <- relabel tA [ByLabel "L" --> ByLabel "R", ByLabel "R" --> ByLabel "L"]
  rewrite "transpose(A) ⇒ relabel(A, swap)" lhs rhs

inverse :: forall a. AnyDTypeRule a
inverse _ = do
  rclass <- newRClass "rclass"
  s1 <- newMap "s1" rclass
  s2 <- newMap "s2" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  lhs <- transpose $ transpose tA
  rewrite "transpose(transpose(A)) ⇒ A" lhs tA

-- transpose(ewadd(x, y)) = ewadd(transpose(x), transpose(y))
transposeEwadd :: forall a. NumRule a
transposeEwadd _ = do
  r <- newRClass "r"
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
  r <- newRClass "r"
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
  r <- newRClass "r"
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
  r <- newRClass "r"
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
  r <- newRClass "r"
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

-- -- ############################# (Rewrite rules enforcing singleton) ############################
-- ############################# (Rewrite rules enforcing singleton) ############################
-- Desugaring for TASO singleton transpose
desugarTransposeSingleton :: forall a. AnyDTypeRule a
desugarTransposeSingleton _ = do
  rclass <- newRClass "rclassS"
  s1 <- newMap "s1S" rclass
  s2 <- newMap "s2S" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  _ <- iota [rclass --> s1] (ByRClass rclass)
  lhs <- transposeSingleton tA
  rhs <- relabel tA [ByLabel "L" --> ByLabel "R", ByLabel "R" --> ByLabel "L"]
  rewrite "transposeSingleton(A) ⇒ relabel(A, swap)" lhs rhs

inverseSingleton :: forall a. AnyDTypeRule a
inverseSingleton _ = do
  rclass <- newRClass "rclassS"
  s1 <- newMap "s1S" rclass
  s2 <- newMap "s2S" rclass
  tA <- newTensor @a "A" [rclass --> s1 @@ "L", rclass --> s2 @@ "R"]
  _ <- iota [rclass --> s1] (ByRClass rclass)
  lhs <- transposeSingleton $ transposeSingleton tA
  rewrite "transposeSingleton(transposeSingleton(A)) ⇒ A" lhs tA

-- transposeSingleton(ewadd(x, y)) = ewadd(transposeSingleton(x), transposeSingleton(y))
transposeSingletonEwadd :: forall a. NumRule a
transposeSingletonEwadd _ = do
  r <- newRClass "rS"
  sL <- newMap "sLS" r
  sR <- newMap "sRS" r
  _ <- iota [r --> sL] (ByRClass r)
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  y <- newTensor @a "y" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transposeSingleton (ewadd x y)
  rhs <- ewadd (transposeSingleton x) (transposeSingleton y)
  rewrite "transposeSingleton(ewadd(x,y)) ⇒ ewadd(transposeSingleton(x), transposeSingleton(y))" lhs rhs

-- transposeSingleton(ewmul(x, y)) = ewmul(transposeSingleton(x), transposeSingleton(y))
transposeSingletonEwmul :: forall a. NumRule a
transposeSingletonEwmul _ = do
  r <- newRClass "rS"
  sL <- newMap "sLS" r
  sR <- newMap "sRS" r
  _ <- iota [r --> sL] (ByRClass r)
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  y <- newTensor @a "y" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transposeSingleton (ewmul x y)
  rhs <- ewmul (transposeSingleton x) (transposeSingleton y)
  rewrite "transposeSingleton(ewmul(x,y)) ⇒ ewmul(transposeSingleton(x), transposeSingleton(y))" lhs rhs

-- transposeSingleton(smul(x, w)) = smul(transposeSingleton(x), w)
transposeSingletonSmul :: forall a. NumRule a
transposeSingletonSmul _ = do
  r <- newRClass "rS"
  sL <- newMap "sLS" r
  sR <- newMap "sRS" r
  _ <- iota [r --> sL] (ByRClass r)
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  let w = ("w" :: a)
  lhs <- transposeSingleton (smul x w)
  rhs <- smul (transposeSingleton x) w
  rewrite "transposeSingleton(smul(x,w)) ⇒ smul(transposeSingleton(x), w)" lhs rhs

-- transposeSingleton(relu(x)) = relu(transposeSingleton(x))
transposeSingletonRelu :: forall a. NumRule a
transposeSingletonRelu _ = do
  r <- newRClass "rS"
  sL <- newMap "sLS" r
  sR <- newMap "sRS" r
  _ <- iota [r --> sL] (ByRClass r)
  x <- newTensor @a "x" [r --> sL @@ "L", r --> sR @@ "R"]
  lhs <- transposeSingleton (relu @a x)
  rhs <- relu @a (transposeSingleton x)
  rewrite "transposeSingleton(relu(x)) ⇒ relu(transposeSingleton(x))" lhs rhs

-- concat(1, transposeSingleton(x), transposeSingleton(y)) = transposeSingleton(concat(0, x, y))
transposeSingletonConcat :: forall a. AnyDTypeRule a
transposeSingletonConcat _ = do
  r <- newRClass "rS"
  sLx <- newMap "sLxS" r
  sRx <- newMap "sRxS" r
  sLy <- newMap "sLyS" r
  sRy <- newMap "sRyS" r
  _ <- iota [r --> sLx] (ByRClass r)
  x <- newTensor @a "x" [r --> sLx @@ "L", r --> sRx @@ "R"]
  y <- newTensor @a "y" [r --> sLy @@ "L", r --> sRy @@ "R"]
  let axis1 = ByLabel "R"
  let axis0 = ByLabel "L"
  lhs <- concat axis1 (transposeSingleton x) (transposeSingleton y)
  rhs <- transposeSingleton (concat axis0 x y)
  rewrite "concat(1, transposeSingleton(x), transposeSingleton(y)) ⇒ transposeSingleton(concat(0, x, y))" lhs rhs

main :: IO ()
main = do
  print "######################## desugarTranspose ########################"
  verifyNumDSL desugarTranspose
  print "######################## inverse #################################"
  verifyNumDSL inverse
  print "######################## transposeEwadd ##########################"
  verifyNumDSL transposeEwadd
  print "######################## transposeEwmul ##########################"
  verifyNumDSL transposeEwmul
  print "######################## transposeSmul ###########################"
  verifyNumDSL transposeSmul
  print "######################## transposeRelu ###########################"
  verifyNumDSL transposeRelu
  print "######################## transposeConcat #########################"
  verifyNumDSL transposeConcat
  print "######################## desugarTransposeSingleton ###############"
  verifyNumDSL desugarTransposeSingleton
  print "######################## inverseSingleton ########################"
  verifyNumDSL inverseSingleton
  print "######################## transposeSingletonEwadd #################"
  verifyNumDSL transposeSingletonEwadd
  print "######################## transposeSingletonEwmul #################"
  verifyNumDSL transposeSingletonEwmul
  print "######################## transposeSingletonSmul ##################"
  verifyNumDSL transposeSingletonSmul
  print "######################## transposeSingletonRelu ##################"
  verifyNumDSL transposeSingletonRelu
  print "######################## transposeSingletonConcat ################"
  verifyNumDSL transposeSingletonConcat
