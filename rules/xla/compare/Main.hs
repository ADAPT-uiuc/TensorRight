module Main (main) where

import qualified Data.Text as T
import Grisette hiding ((-->))
import TensorRight

constructRule :: forall a. T.Text -> CompareOp -> Bool -> NumRule a
constructRule name op value _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- compareOp op tA tA
  rhs <- constant @SymBool (con value) [rclass --> map]
  rewrite name lhs rhs

rule01 :: forall a. NumRule a
rule01 = constructRule "Gt(A, A) ⇒ False" Gt False

rule02 :: forall a. NumRule a
rule02 = constructRule "Lt(A, A) ⇒ False" Lt False

rule03 :: forall a. NumRule a
rule03 = constructRule "Ne(A, A) ⇒ False" Ne False

rule04 :: forall a. NumRule a
rule04 = constructRule "Ge(A, A) ⇒ True" Ge True

rule05 :: forall a. NumRule a
rule05 = constructRule "Le(A, A) ⇒ True" Le True

rule06 :: forall a. NumRule a
rule06 = constructRule "Eqv(A, A) ⇒ True" Eqv True

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyNumDSL rule03
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
