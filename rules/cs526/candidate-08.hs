module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight

rule04 :: forall a. NumRule a
rule04 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tP <- newTensor @SymBool "P" [rclass --> map]
  tX <- newTensor @a "X" [rclass --> map]
  tY <- newTensor @a "Y" [rclass --> map]
  tZ <- newTensor @a "Z" [rclass --> map]
  lhs <- select tP (numBinOp Add tX tZ) (numBinOp Add tY tZ)
  rhs <- numBinOp Add (select tP tX tY) tZ
  rewrite "Select(P, Add(X, Z), Add(Y, Z)) ==> Add(Select(P, X, Y), Z)" lhs rhs

rule03_v1 :: forall a. NumRule a
rule03_v1 _ = do
  [rcXSpatial, rcXRev, rcYSpatial, rcYRev, rcContract, rcBatch] <- newRClasses ["rcXSpatial", "rcXRev", "rcYSpatial", "rcYRev", "rcContract", "rcBatch"]
  rcXSpatialSize <- newMap "rcXSpatialSize" rcXSpatial
  rcXRevSize <- newMap "rcXRevSize" rcXRev
  rcYSpatialSize <- newMap "rcYSpatialSize" rcYSpatial
  rcYRevSize <- newMap "rcYRevSize" rcYRev
  rcContractSize <- newMap "rcContractSize" rcContract
  rcBatchSize <- newMap "rcBatchSize" rcBatch
  [siL, siR] <- newMaps ["siL", "siR"] rcContract
  tX <- newTensor @a "X" [rcXSpatial --> rcXSpatialSize, rcXRev --> rcXRevSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  tY <- newTensor @a "Y" [rcYSpatial --> rcYSpatialSize, rcYRev --> rcYRevSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize]
  lhs <- reverseTensor (dot tX tY [rcContract --> siL] [ByRClass rcBatch]) [ByRClass rcXRev, ByRClass rcYRev]
  rhs <- dot (reverseTensor tX [ByRClass rcXRev]) (reverseTensor tY [ByRClass rcYRev]) [rcContract --> siR] [ByRClass rcBatch]
  siRelation [siL, siR] $ \[siL, siR] -> siL .== siR
  checkSIMap [siL] [siR]
  rewrite "Rev(Dot(X, Y, C, B), dims) ==> Dot(Rev(X, dims1), Rev(Y, dims2), C, B)" lhs rhs

rule03_v2 :: forall a. NumRule a
rule03_v2 _ = do
  [rcXSpatial, rcYSpatial, rcContract, rcContractRev, rcBatch] <- newRClasses ["rcXSpatial", "rcYSpatial", "rcContract", "rcContractRev", "rcBatch"]
  rcXSpatialSize <- newMap "rcXSpatialSize" rcXSpatial
  rcYSpatialSize <- newMap "rcYSpatialSize" rcYSpatial
  rcContractSize <- newMap "rcContractSize" rcContract
  rcContractRevSize <- newMap "rcContractRevSize" rcContractRev
  rcBatchSize <- newMap "rcBatchSize" rcBatch
  [siL, siR] <- newMaps ["siL", "siR"] rcContract
  [siRevL, siRevR] <- newMaps ["siRevL", "siRevR"] rcContractRev
  tX <- newTensor @a "X" [rcXSpatial --> rcXSpatialSize, rcContract --> rcContractSize, rcContractRev --> rcContractRevSize, rcBatch --> rcBatchSize]
  tY <- newTensor @a "Y" [rcYSpatial --> rcYSpatialSize, rcContract --> rcContractSize, rcContractRev --> rcContractRevSize, rcBatch --> rcBatchSize]
  lhs <- dot (reverseTensor tX [ByRClass rcContractRev]) (reverseTensor tY [ByRClass rcContractRev]) [rcContract --> siL, rcContractRev --> siRevL] [ByRClass rcBatch]
  rhs <- dot tX tY [rcContract --> siR, rcContractRev --> siRevR] [ByRClass rcBatch]
  siRelation [siL, siR] $ \[siL, siR] -> siL .== siR
  siRelation [siRevL, siRevR, rcContractRevSize] $ \[siL, siR, size] -> siR .== size - siL - 1
  checkSIMap [siL, siRevL] [siR, siRevR]
  rewrite "Dot(Rev(X, C2), Rev(Y, C2), C1 ∪ C2, B) ==> Dot(X, Y, C1 ∪ C2, B)" lhs rhs

rule03_v3 :: forall a. NumRule a
rule03_v3 _ = do
  [rcXSpatial, rcYSpatial, rcContract, rcBatch, rcBatchRev] <- newRClasses ["rcXSpatial", "rcYSpatial", "rcContract", "rcBatch", "rcBatchRev"]
  rcXSpatialSize <- newMap "rcXSpatialSize" rcXSpatial
  rcYSpatialSize <- newMap "rcYSpatialSize" rcYSpatial
  rcContractSize <- newMap "rcContractSize" rcContract
  rcBatchSize <- newMap "rcBatchSize" rcBatch
  rcBatchRevSize <- newMap "rcBatchRevSize" rcBatchRev
  [siL, siR] <- newMaps ["siL", "siR"] rcContract
  tX <- newTensor @a "X" [rcXSpatial --> rcXSpatialSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize, rcBatchRev --> rcBatchRevSize]
  tY <- newTensor @a "Y" [rcYSpatial --> rcYSpatialSize, rcContract --> rcContractSize, rcBatch --> rcBatchSize, rcBatchRev --> rcBatchRevSize]
  lhs <- dot (reverseTensor tX [ByRClass rcBatchRev]) (reverseTensor tY [ByRClass rcBatchRev]) [rcContract --> siL] [ByRClass rcBatch, ByRClass rcBatchRev]
  rhs <- reverseTensor (dot tX tY [rcContract --> siR] [ByRClass rcBatch, ByRClass rcBatchRev]) [ByRClass rcBatchRev]
  siRelation [siL, siR] $ \[siL, siR] -> siL .== siR
  checkSIMap [siL] [siR]
  rewrite "Dot(Rev(X, B2), Rev(Y, B2), C, B1 ∪ B2) ==> Rev(Dot(X, Y, C, B1 ∪ B2), B2)" lhs rhs

main :: IO ()
main = do
  print "############################## rule04 ##############################"
  verifyNumDSL rule04
  print "############################## rule03_v1 ##############################"
  verifyNumDSL rule03_v1
  print "############################## rule03_v2 ##############################"
  verifyNumDSL rule03_v2
  print "############################## rule03_v3 ##############################"
  verifyNumDSL rule03_v3
