module Main (main) where

import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  [rclass] <- newRClasses ["rclass"]
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map]
  lhs <-
    relabel
      (relabel tensor [rclass --> ByLabel "label"])
      [ByLabel "label" --> ByLabel "label2"]
  rhs <- relabel tensor [rclass --> ByLabel "label2"]
  rewrite "Transpose(Transpose(A)) ⇒ Transpose(A)" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass] <- newRClasses ["rclass"]
  map <- newMap "map" rclass
  tensor <- newTensor @a "tensor" [rclass --> map @@ "label"]
  lhs <- relabel tensor [ByLabel "label" --> ByLabel "label"]
  let rhs = tensor
  rewrite "Transpose(A) ⇒ A" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
