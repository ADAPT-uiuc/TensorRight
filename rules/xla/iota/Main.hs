module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: DSLContext Rewrite
rule01 = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  rc0Size <- newMap "rc0Size" rclass0
  rc1Size <- newMap "rc1Size" rclass1

  lhs <- iota [rclass0 --> rc0Size, rclass1 --> rc1Size] (ByRClass rclass0)
  precondition [rc0Size] $ \[s] -> s .== 1

  rhs <- constant @TensorInt 0 [rclass0 --> rc0Size, rclass1 --> rc1Size]
  rewrite "Iota ⇒ Zero" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyDSL rule01
