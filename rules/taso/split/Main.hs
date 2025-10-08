module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (checkSIMap, monitorExprOnFailure, newRClasses, siRelation)
import TensorRight.Internal.DSL.TASO (concat, split0, split1)
import Prelude hiding (concat)

rule_split0 :: forall a. NumRule a -- Verify desugaring
rule_split0 _ = do
  [rclassM, rclassN] <- newRClasses ["rclassM", "rclassN"]
  sizeM1 <- newMap "sizeM1" rclassM
  sizeM2 <- newMap "sizeM2" rclassM

  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM1, rclassN --> sizeN]
  y <- newTensor @a "y" [rclassM --> sizeM2, rclassN --> sizeN]

  let concatAxis = ByRClass rclassN
  lhs <- split0 concatAxis $ concat concatAxis x y
  let rhs = x

  rewrite "split_0(a, concat(a, x, y)) ⇒ x" lhs rhs

rule_split1 :: forall a. NumRule a -- Verify desugaring
rule_split1 _ = do
  [rclassM, rclassN] <- newRClasses ["rclassM", "rclassN"]
  sizeM1 <- newMap "sizeM1" rclassM
  sizeM2 <- newMap "sizeM2" rclassM

  sizeN <- newMap "sizeN" rclassN

  x <- newTensor @a "x" [rclassM --> sizeM1, rclassN --> sizeN]
  y <- newTensor @a "y" [rclassM --> sizeM2, rclassN --> sizeN]

  let concatAxis = ByRClass rclassN
  lhs <- split1 concatAxis $ concat concatAxis x y
  let rhs = y

  rewrite "split_1(a, concat(a, x, y)) ⇒ y" lhs rhs

main :: IO ()
main = do
  printTitle "#################### split0 ####################"
  verifyNumDSL rule_split0
  printTitle "#################### split1 ####################"
  verifyNumDSL rule_split1