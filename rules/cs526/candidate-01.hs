module Main (main) where

import qualified Data.HashMap.Lazy as HM
import Grisette hiding (dot, (-->))
import TensorRight

rule02 :: forall a. NumRule a
rule02 _ = do
  [rcX, rcY, rcContract, rcBatch, rcNew] <- newRClasses ["rcX", "rcY", "rcContract", "rcBatch", "rcNew"]
  rcXSize <- newMap "rcXSize" rcX
  rcYSize <- newMap "rcYSize" rcY
  rcContractSize <- newMap "rcContractSize" rcContract
  rcBatchSize <- newMap "rcBatchSize" rcBatch
  rcNewSize <- newMap "rcNewSize" rcNew
  [siContractL, siContractR] <- newMaps ["siContractL", "siContractR"] rcContract
  tX <- newTensor @a "X" [rcX --> rcXSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  tY <- newTensor @a "Y" [rcY --> rcYSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  lhs <- dot (broadcast tX [rcNew --> rcNewSize]) (broadcast tY [rcNew --> rcNewSize]) [rcContract --> siContractL] [ByRClass rcBatch, ByRClass rcNew]
  rhs <- broadcast (dot tX tY [rcContract --> siContractR] [ByRClass rcBatch]) [rcNew --> rcNewSize]
  siRelation [siContractL, siContractR] $ \[l, r] -> l .== r
  checkSIMap [siContractL] [siContractR]
  rewrite "Dot(Broadcast(X, S), Broadcast(Y, S), C, B ∪ S) ==> Broadcast(Dot(X, Y, C, B), S)" lhs rhs

rule03 :: forall a. AnyDTypeRule a
rule03 _ = do
  [rclass0, rclass1] <- newRClasses ["rclass0", "rclass1"]
  sizeMap0 <- newMap "sizeMap" rclass0
  sizeMap1 <- newMap "sizeMap" rclass1
  tP <- newTensor @SymBool "P" [rclass0 --> sizeMap0]
  tX <- newTensor @a "X" [rclass0 --> sizeMap0]
  tY <- newTensor @a "Y" [rclass0 --> sizeMap0]
  tP' <- broadcast tP [rclass1 --> sizeMap1]
  tX' <- broadcast tX [rclass1 --> sizeMap1]
  tY' <- broadcast tY [rclass1 --> sizeMap1]
  lhs <- select tP' tX' tY'
  rhs <- broadcast (select tP tX tY) [rclass1 --> sizeMap1]
  rewrite "Select(Broadcast(P, S), Broadcast(X, S), Broadcast(Y, S)) ==> Broadcast(Select(P, X, Y), S)" lhs rhs

rule05 :: forall a. NumRule a
rule05 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @a "X" [rclass --> sizeMap]
  tY <- newTensor @a "Y" [rclass --> sizeMap]
  lhs <- numBinOp Add tX (numBinOp Mul tX tY)
  rhs <- numBinOp Mul tX (numBinOp Add (constant @a 1 [rclass --> sizeMap]) tY)
  rewrite "Add(X, Mul(X, Y)) ==> Mul(X, Add(1, Y))" lhs rhs

rule06 :: forall a. NumRule a
rule06 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @a "X" [rclass --> sizeMap]
  lhs <- numBinOp Add tX (numUnaryOp Neg tX)
  rhs <- constant @a 0 [rclass --> sizeMap]
  rewrite "Add(X, Neg(X)) ==> 0" lhs rhs

rule07 :: forall a. AnyDTypeRule a
rule07 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  [innerLow, innerHigh, innerInterior] <- newMaps ["innerLow", "innerHigh", "innerInterior"] rclass
  [outerLow, outerHigh, outerInterior] <- newMaps ["outerLow", "outerHigh", "outerInterior"] rclass
  rhsLow <- combineMap "rhsLow" sum [innerLow, outerLow]
  rhsHigh <- combineMap "rhsHigh" sum [innerHigh, outerHigh]
  rhsInterior <- combineMap "rhsInterior" sum [innerInterior, outerInterior]
  tX <- newTensor @a "X" [rclass --> sizeMap]
  let innerPadConfig =
        Padding
          { low = [rclass --> innerLow],
            interior = [rclass --> innerInterior],
            high = [rclass --> innerHigh]
          }
  let outerPadConfig =
        Padding
          { low = [rclass --> outerLow],
            interior = [rclass --> outerInterior],
            high = [rclass --> outerHigh]
          }
  let rhsPadConfig =
        Padding
          { low = [rclass --> rhsLow],
            interior = [rclass --> rhsInterior],
            high = [rclass --> rhsHigh]
          }
  lhs <- pad (pad tX ("a" :: a) innerPadConfig) ("a" :: a) outerPadConfig
  rhs <- pad tX ("a" :: a) rhsPadConfig
  rewrite "Pad(Pad(X, a, L1, H1, I1), a, L2, H2, I2) ==> Pad(X, a, L1 + L2, H1 + H2, I1 + I2)" lhs rhs

rule07_v1 :: forall a. AnyDTypeRule a
rule07_v1 _ = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  [innerLow, innerHigh, innerInterior] <- newMaps ["innerLow", "innerHigh", "innerInterior"] rclass
  [outerLow, outerHigh, outerInterior] <- newMaps ["outerLow", "outerHigh", "outerInterior"] rclass
  rhsLow <- combineMap "rhsLow" sum [innerLow, outerLow]
  rhsHigh <- combineMap "rhsHigh" sum [innerHigh, outerHigh]
  rhsInterior <- combineMap "rhsInterior" sum [innerInterior, outerInterior]
  tX <- newTensor @a "X" [rclass --> sizeMap]
  -- TODO: Generalize to non-zero outer interior padding
  precondition [outerInterior] $ \[o] -> o .== 0
  precondition [innerLow, outerLow] $
    \[il, ol] -> symNot (il .< 0 .&& ol .> 0)
  precondition [innerHigh, outerHigh] $
    \[ih, oh] -> symNot (ih .< 0 .&& oh .> 0)
  let innerPadConfig =
        Padding
          { low = [rclass --> innerLow],
            interior = [rclass --> innerInterior],
            high = [rclass --> innerHigh]
          }
  let outerPadConfig =
        Padding
          { low = [rclass --> outerLow],
            interior = [rclass --> outerInterior],
            high = [rclass --> outerHigh]
          }
  let rhsPadConfig =
        Padding
          { low = [rclass --> rhsLow],
            interior = [rclass --> rhsInterior],
            high = [rclass --> rhsHigh]
          }
  lhs <- pad (pad tX ("a" :: a) innerPadConfig) ("a" :: a) outerPadConfig
  rhs <- pad tX ("a" :: a) rhsPadConfig
  rewrite "Pad(Pad(X, a, L1, H1, I1), a, L2, H2, I2) ==> Pad(X, a, L1 + L2, H1 + H2, I1 + I2) if I1 = 0 and I2 = 0" lhs rhs

rule09 :: DSLContext Rewrite
rule09 = do
  rclass <- newRClass "rclass"
  sizeMap <- newMap "sizeMap" rclass
  tX <- newTensor @TensorReal "X" [rclass --> sizeMap]
  tY <- newTensor @TensorReal "Y" [rclass --> sizeMap]
  tZ <- newTensor @TensorReal "Z" [rclass --> sizeMap]
  lhs <- numBinOp Sub (numBinOp Div tX tY) (numBinOp Div tZ tY)
  rhs <- numBinOp Div (numBinOp Sub tX tZ) tY
  rewrite "Sub(Div(X, Y), Div(Z, Y)) ==> Div(Sub(X, Z), Y)" lhs rhs

rule10 :: forall a. NumRule a
rule10 _ = do
  [rcX, rcY, rcContract, rcBatch, rcNew] <- newRClasses ["rcX", "rcY", "rcContract", "rcBatch", "rcNew"]
  rcXSize <- newMap "rcXSize" rcX
  rcYSize <- newMap "rcYSize" rcY
  rcContractSize <- newMap "rcContractSize" rcContract
  rcBatchSize <- newMap "rcBatchSize" rcBatch
  rcNewSize <- newMap "rcNewSize" rcNew
  [siContractL, siContractR] <- newMaps ["siContractL", "siContractR"] rcContract
  tX <- newTensor @a "X" [rcX --> rcXSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  tY <- newTensor @a "Y" [rcY --> rcYSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  lhs <- dot (broadcast tX [rcNew --> rcNewSize]) tY [rcContract --> siContractL] [ByRClass rcBatch]
  rhs <- broadcast (dot tX tY [rcContract --> siContractR] [ByRClass rcBatch]) [rcNew --> rcNewSize]
  siRelation [siContractL, siContractR] $ \[l, r] -> l .== r
  checkSIMap [siContractL] [siContractR]
  rewrite "Dot(Broadcast(X, S), Y, C, B) ==> Broadcast(Dot(X, Y, C, B), S)" lhs rhs

main :: IO ()
main = do
  print "############################## rule02 ##############################"
  verifyNumDSL rule02
  print "############################## rule03 ##############################"
  verifyAnyDTypeDSL rule03
  print "############################## rule05 ##############################"
  verifyNumDSL rule05
  print "############################## rule06 ##############################"
  verifyNumDSL rule06
  print "############################## rule07 ##############################"
  verifyAnyDTypeDSL rule07
  print "############################## rule07_v1 ##############################"
  verifyAnyDTypeDSL rule07_v1
  print "############################## rule09 ##############################"
  verifyDSL rule09
  print "############################## rule10 ##############################"
  verifyNumDSL rule10
