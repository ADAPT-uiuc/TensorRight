module Main (main) where

import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <-
    relabel
      (relabel tA [rclass --> ByLabel "label"])
      [ByLabel "label" --> ByLabel "label2"]
  rhs <- relabel tA [rclass --> ByLabel "label2"]
  rewrite "Transpose(Transpose(A)) ⇒ Transpose(A)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map @@ "label"]
  lhs <- relabel tA [ByLabel "label" --> ByLabel "label"]
  let rhs = tA
  rewrite "Transpose(A) ⇒ A" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
