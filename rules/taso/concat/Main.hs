{-# OPTIONS_GHC -Wno-missing-import-lists #-}

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, relu, smul)
import Prelude hiding (concat)

desugar :: forall a. NumRule a
desugar _ = do
  r <- newRClass "r"
  [sa, sb] <- newMaps ["sa", "sb"] r
  a <- newTensor @a "A" [r --> sa]
  b <- newTensor @a "B" [r --> sb]
  let d = ByRClass r
  lhs <- concat d a b
  rhs <- concatTensor a b d
  rewrite "concat(d, A, B) ⇒ Concatenate((A, B), d)" lhs rhs

smulAssociativity :: forall a. NumRule a
smulAssociativity _ = do
  let w = ("w" :: a)
  r <- newRClass "r"
  s <- newMap "s" r
  x <- newTensor @a "x" [r --> s]
  y <- newTensor @a "y" [r --> s]
  let d = ByRClass r
  lhs <- concat d (smul x w) (smul y w)
  rhs <- smul (concat d x y) w
  rewrite "concat(d, smul(x, w), smul(y, w)) ⇒ smul(concat(d, x, y), w)" lhs rhs

ewaddAssociativity :: forall a. NumRule a
ewaddAssociativity _ = do
  r <- newRClass "r"
  s <- newMap "s" r
  x <- newTensor @a "x" [r --> s]
  y <- newTensor @a "y" [r --> s]
  z <- newTensor @a "z" [r --> s]
  w <- newTensor @a "w" [r --> s]
  let d = ByRClass r
  lhs <- concat d (ewadd x y) (ewadd z w)
  rhs <- ewadd (concat d x z) (concat d y w)
  rewrite "concat(d, ewadd(x, y), ewadd(z, w)) ⇒ ewadd(concat(d, x, z), concat(d, y, w))" lhs rhs

ewmulAssociativity :: forall a. NumRule a
ewmulAssociativity _ = do
  r <- newRClass "r"
  s <- newMap "s" r
  x <- newTensor @a "x" [r --> s]
  y <- newTensor @a "y" [r --> s]
  z <- newTensor @a "z" [r --> s]
  w <- newTensor @a "w" [r --> s]
  let d = ByRClass r
  lhs <- concat d (ewmul x y) (ewmul z w)
  rhs <- ewmul (concat d x z) (concat d y w)
  rewrite "concat(d, ewmul(x, y), ewmul(z, w)) ⇒ ewmul(concat(d, x, z), concat(d, y, w))" lhs rhs

reluAssociativity :: forall a. NumRule a
reluAssociativity _ = do
  r <- newRClass "r"
  s <- newMap "s" r
  x <- newTensor @a "x" [r --> s]
  y <- newTensor @a "y" [r --> s]
  let d = ByRClass r
  lhs <- concat d (relu @a x) (relu @a y)
  rhs <- relu @a $ concat d x y
  rewrite "" lhs rhs

geometry :: forall a. NumRule a
geometry _ = do
  [d0, d1, d2] <- newRClasses ["d0", "d1", "d2"]
  d0S <- newMap "d0S" d0
  d1S <- newMap "d1S" d1
  d2S <- newMap "d2S" d2
  x <- newTensor @a "x" [d0 --> d0S, d1 --> d1S, d2 --> d2S]
  y <- newTensor @a "y" [d0 --> d0S, d1 --> d1S, d2 --> d2S]
  z <- newTensor @a "z" [d0 --> d0S, d1 --> d1S, d2 --> d2S]
  w <- newTensor @a "w" [d0 --> d0S, d1 --> d1S, d2 --> d2S]
  lhs <- concat (ByRClass d0) (concat (ByRClass d1) x y) (concat (ByRClass d1) z w)
  rhs <- concat (ByRClass d1) (concat (ByRClass d0) x z) (concat (ByRClass d0) y w)
  rewrite "concat(d0, concat(d1, x, y), concat(d1, z, w)) ⇒ concat(d1, concat(d0, x, z), concat(0, y, w))" lhs rhs

main :: IO ()
main = do
  printTitle "######################## desugarOneRole ########################"
  verifyNumDSL desugar
  printTitle "######################## smulAssociativity #####################"
  verifyNumDSL smulAssociativity
  printTitle "######################## ewaddAssociativity ####################"
  verifyNumDSL ewaddAssociativity
  printTitle "######################## ewmulAssociativity ####################"
  verifyNumDSL ewmulAssociativity
  printTitle "######################## reluAssociativity ####################"
  verifyNumDSL reluAssociativity
  printTitle "######################## geometry #############################"
  verifyNumDSL geometry
