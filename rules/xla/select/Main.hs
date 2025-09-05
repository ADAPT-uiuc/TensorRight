module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. AnyDTypeRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- select tP tA tA
  let rhs = tA
  rewrite "Select(P, A, A) ⇒ A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool true [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- select pred tA tB
  let rhs = tA
  rewrite "Select(True, A, B) ⇒ A" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool false [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- select pred tA tB
  let rhs = tB
  rewrite "Select(False, A, B) ⇒ B" lhs rhs

rule04 :: forall a. AnyDTypeRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  pred <- constant @SymBool false [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  tB <- newTensor @a "B" [rclass --> map]
  lhs <- select (boolUnaryOp Not pred) tA tB
  rhs <- select pred tB tA
  rewrite "Select(Not(P), A, B) ⇒ Select(P, B, A)" lhs rhs

-- Select(P, A, DynamicUpdateSlice(A, B, start)) can select only the updated
-- region before re-inserting it. XLA also handles the symmetric arm ordering.
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L9914-L9956
rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB, rcStart] <- newMaps ["rcSizeA", "rcSizeB", "rcStart"] rclass
  tP <- newTensor @SymBool "P" [rclass --> rcSizeA]
  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <- select tP tA (dynamicUpdateSlice tA tB [rclass --> rcStart])
  tPSlice <- dynamicSlice tP $ DySlice {start = [rclass --> rcStart], sizes = [rclass --> rcSizeB]}
  tASlice <- dynamicSlice tA $ DySlice {start = [rclass --> rcStart], sizes = [rclass --> rcSizeB]}
  rhs <- dynamicUpdateSlice tA (select tPSlice tASlice tB) [rclass --> rcStart]
  rewrite "Select(P, A, DynamicUpdateSlice(A, B, ...)) ⇒ DynamicUpdateSlice(A, Select(DynamicSlice(P), DynamicSlice(A), B), ...)" lhs rhs

-- Symmetric form of rule05.
-- https://github.com/openxla/xla/blob/cb214917224f5643aa8efc96823a920c42f47336/xla/hlo/transforms/simplifiers/algebraic_simplifier.cc#L9914-L9956
rule06 :: forall a. AnyDTypeRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  [rcSizeA, rcSizeB, rcStart] <- newMaps ["rcSizeA", "rcSizeB", "rcStart"] rclass
  tP <- newTensor @SymBool "P" [rclass --> rcSizeA]
  tA <- newTensor @a "A" [rclass --> rcSizeA]
  tB <- newTensor @a "B" [rclass --> rcSizeB]
  lhs <- select tP (dynamicUpdateSlice tA tB [rclass --> rcStart]) tA
  tPSlice <- dynamicSlice tP $ DySlice {start = [rclass --> rcStart], sizes = [rclass --> rcSizeB]}
  tASlice <- dynamicSlice tA $ DySlice {start = [rclass --> rcStart], sizes = [rclass --> rcSizeB]}
  rhs <- dynamicUpdateSlice tA (select tPSlice tB tASlice) [rclass --> rcStart]
  rewrite "Select(P, DynamicUpdateSlice(A, B, ...), A) ⇒ DynamicUpdateSlice(A, Select(DynamicSlice(P), B, DynamicSlice(A)), ...)" lhs rhs

main :: IO ()
main = do
  printTitle "############################## rule01 ##############################"
  verifyAnyDTypeDSL rule01
  printTitle "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  printTitle "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  printTitle "############################## rule04 ##############################"
  verifyAnyDTypeDSL rule04
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
  print "############################## rule06 ##############################"
  verifyAnyDTypeDSL rule06
