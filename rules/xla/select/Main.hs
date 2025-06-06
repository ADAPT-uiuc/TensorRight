module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- newTensor @SymBool "pred" [rclass --> map]
  a <- newTensor @a "a" [rclass --> map]
  lhs <- select pred a a
  let rhs = a
  rewrite "Select(P,A,A) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool true [rclass --> map]
  a <- newTensor @a "a" [rclass --> map]
  b <- newTensor @a "b" [rclass --> map]
  lhs <- select pred a b
  let rhs = a
  rewrite "Select(True,A,B) ⇒ A" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool false [rclass --> map]
  a <- newTensor @a "a" [rclass --> map]
  b <- newTensor @a "b" [rclass --> map]
  lhs <- select pred a b
  let rhs = b
  rewrite "Select(False,A,B) ⇒ B" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool false [rclass --> map]
  a <- newTensor @a "a" [rclass --> map]
  b <- newTensor @a "b" [rclass --> map]
  lhs <- select (boolUnaryOp Not pred) a b
  rhs <- select pred b a
  rewrite "Select(Not(P),A,B) ⇒ Select(P,B,A)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
