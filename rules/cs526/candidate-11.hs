module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  lhs <- numBinOp Div (numBinOp Add tX tX) (constant @a 2 [rclass --> map])
  let rhs = tX
  rewrite "Div(Add(X, X), 2) ==> X" lhs rhs

rule02 :: forall a. NumRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- select (compareOp Ge tX (constant @a 0 [rclass --> map])) tY tZ
  rhs <- numBinOp Max tY tZ
  rewrite "Select(Ge(tX, 0), Y, Z) ==> Max(Y, Z)" lhs rhs

rule03 :: forall a. NumRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- select (compareOp Lt tX (constant @a 0 [rclass --> map])) tY tZ
  rhs <- numBinOp Min tY tZ
  rewrite "Select(Lt(tX, 0), Y, Z) ==> Min(Y, Z)" lhs rhs

rule08 :: forall a. AnyDTypeRule a
rule08 _ = do
  rclass <- newRClass "rclass"
  [size, low, high, interior] <- newMaps ["size", "low", "high", "interior"] rclass
  tP <- newTensor @SymBool "P" [rclass --> size]
  tX <- newTensor @a "X" [rclass --> size]
  tY <- newTensor @a "Y" [rclass --> size]
  pPad <-
    pad tP (con True :: SymBool) $
      Padding
        { low = [rclass --> low],
          interior = [rclass --> interior],
          high = [rclass --> high]
        }
  pX <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass --> low],
          interior = [rclass --> interior],
          high = [rclass --> high]
        }
  pY <-
    pad tY ("a" :: a) $
      Padding
        { low = [rclass --> low],
          interior = [rclass --> interior],
          high = [rclass --> high]
        }
  lhs <- select pPad pX pY
  rhs <-
    pad (select tP tX tY) ("a" :: a) $
      Padding
        { low = [rclass --> low],
          interior = [rclass --> interior],
          high = [rclass --> high]
        }
  rewrite "Select(Pad(P, True, low, high, int), Pad(X, v, low, high, int), Pad(Y, v, low, high, int)) ==> Pad(Select(P, X, Y), v, low, high, int)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule08 ##############################"
  verifyAnyDTypeDSL rule08
