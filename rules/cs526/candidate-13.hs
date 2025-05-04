module Main (main) where

import Grisette hiding ((-->))
import TensorRight

rule01 :: forall a. NumRule a
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- clamp tA tX tA
  rhs <- numBinOp Max tX tA
  rewrite "Clamp(A, X, A) ==> Max(X, A)" lhs rhs

rule01_correct :: forall a. NumRule a
rule01_correct _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tX <- newTensor @a "X" [rclass --> map]
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- clamp tA tX tA
  let rhs = tA
  rewrite "Clamp(A, X, A) ==> A" lhs rhs

rule02 :: forall a. AnyDTypeRule a
rule02 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  lhs <- reverseTensor tXPad [ByRClass rclass0]
  rhs <-
    pad (reverseTensor tX [ByRClass rclass0]) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rewrite "Rev(Pad(X, v, S_l, S_h, S_i), dims) ==> Pad(Rev(X, dims), v, S_l, S_h, S_i)" lhs rhs

rule02_v1_forward :: forall a. AnyDTypeRule a
rule02_v1_forward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  lhs <- reverseTensor tXPad [ByRClass rclass0]
  rhs <-
    pad (reverseTensor tX [ByRClass rclass0]) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0High, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Low, rclass1 --> rc1High]
        }
  precondition [rc0Int] $ \[int] -> int .== 0
  precondition [rc1Int] $ \[int] -> int .== 0
  rewrite "Rev(Pad(X, v, S_l, S_h, S_i), dims) ==> Pad(Rev(X, dims), v, S_h, S_l, S_i) if S_i = 0" lhs rhs

rule02_v1_backward :: forall a. AnyDTypeRule a
rule02_v1_backward _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  lhs <-
    pad (reverseTensor tX [ByRClass rclass0]) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0High, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Low, rclass1 --> rc1High]
        }
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  rhs <- reverseTensor tXPad [ByRClass rclass0]
  precondition [rc0Int] $ \[int] -> int .== 0
  precondition [rc1Int] $ \[int] -> int .== 0
  rewrite "Pad(Rev(X, dims), v, S_h, S_l, S_i) ==> Rev(Pad(X, v, S_l, S_h, S_i), dims) if S_i = 0" lhs rhs

rule02_v2 :: forall a. AnyDTypeRule a
rule02_v2 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  [rc0Size, rc0Low, rc0High, rc0Int] <- newMaps ["rc0Size", "rc0Low", "rc0High", "rc0Int"] rclass0
  [rc1Size, rc1Low, rc1High, rc1Int] <- newMaps ["rc1Size", "rc1Low", "rc1High", "rc1Int"] rclass1
  tX <- newTensor @a "X" [rclass0 --> rc0Size, rclass1 --> rc1Size]
  tXPad <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0Low, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0High, rclass1 --> rc1High]
        }
  lhs <- reverseTensor tXPad [ByRClass rclass0]
  rhs <-
    pad (reverseTensor tX [ByRClass rclass0]) ("a" :: a) $
      Padding
        { low = [rclass0 --> rc0High, rclass1 --> rc1Low],
          interior = [rclass0 --> rc0Int, rclass1 --> rc1Int],
          high = [rclass0 --> rc0Low, rclass1 --> rc1High]
        }
  rewrite "Rev(Pad(X, v, S_l, S_h, S_i), dims) ==> Pad(Rev(X, dims), v, S_h, S_l, S_i)" lhs rhs

rule05 :: forall a. AnyDTypeRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  [size, lowIn, highIn, lowOut, highOut] <- newMaps ["size", "lowIn", "highIn", "lowOut", "highOut"] rclass
  [interiorIn, interiorOut] <- newConstMaps ["interiorIn", "interiorOut"] 1 rclass
  tX <- newTensor @a "X" [rclass --> size]
  let innerPadding =
        Padding
          { low = [rclass --> lowIn],
            interior = [rclass --> interiorIn],
            high = [rclass --> highIn]
          }
  let outerPadding =
        Padding
          { low = [rclass --> lowOut],
            interior = [rclass --> interiorOut],
            high = [rclass --> highOut]
          }
  lhs <- pad (pad tX ("a" :: a) innerPadding) ("a" :: a) outerPadding
  rhs <-
    pad tX ("a" :: a) $
      Padding
        { low = [rclass --> lowIn],
          interior = [rclass --> interiorOut],
          high = [rclass --> highIn]
        }
  precondition [lowIn, lowOut] $ \[i, o] -> i .== o
  precondition [highIn, highOut] $ \[i, o] -> i .== o
  rewrite "Pad(Pad(X, 1, S_l, S_h, S_i), 1, S_l_rhs, S_h_rhs, S_i_rhs) ==> Pad(X, 1, S_l, S_h, S_i_rhs)\n  if S_i = 1 && S_i_rhs = 1 && S_l = S_l_rhs && S_h = S_h_rhs" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01
  print "############################## rule01_correct ##############################"
  verifyNumDSL rule01_correct
  print "############################## rule02 ##############################"
  verifyAnyDTypeDSL rule02
  print "############################## rule02_v1_forward ##############################"
  verifyAnyDTypeDSL rule02_v1_forward
  print "############################## rule02_v1_backward ##############################"
  verifyAnyDTypeDSL rule02_v1_backward
  print "############################## rule02_v2 ##############################"
  verifyAnyDTypeDSLWith (withTimeout 10000000 z3) rule02_v2
  print "############################## rule05 ##############################"
  verifyAnyDTypeDSL rule05
