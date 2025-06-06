module Main (main) where

import TensorRight

rule01 :: DSLContext Rewrite
rule01 = do
  rclass <- newRClass "rclass"
  size <- newConstMap "size" 1 rclass

  lhs <- iota [rclass --> size] (ByRClass rclass)
  rhs <- constant @TensorInt 0 [rclass --> size]
  rewrite "Iota ⇒ Zero" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyDSL rule01
