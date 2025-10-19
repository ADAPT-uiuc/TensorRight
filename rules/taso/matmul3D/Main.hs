module Main (main) where

import Grisette hiding (dot, (-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (checkSIMap, monitorExprOnFailure, newSingletonRClass, newSingletonRClasses, siRelation)
import TensorRight.Internal.DSL.TASO (concat, ewadd, ewmul, matmul3D, relu, smul, transpose)
import Prelude hiding (concat)

-- | Rule 1: Matrix multiplication associativity (batched)
matmulAssociativity :: forall a. NumRule a
matmulAssociativity _ = do
  [rclassB, rclassM, rclassK, rclassN, rclassP] <- newSingletonRClasses ["rclassB", "rclassM", "rclassK", "rclassN", "rclassP"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN
  sizeP <- newMap "sizeP" rclassP
  [sizeB1, sizeB2, sizeB3] <- newMaps ["sizeB1", "sizeB2", "sizeB3"] rclassB

  -- x:[B,M,K], y:[B,K,N], z:[B,N,P]
  x <- newTensor @a "x" [rclassB --> sizeB1, rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassK --> sizeK, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassB --> sizeB3, rclassN --> sizeN, rclassP --> sizeP]

  -- independent contraction maps for K and N
  kL <- newMap "kL" rclassK
  kR <- newMap "kR" rclassK
  nL <- newMap "nL" rclassN
  nR <- newMap "nR" rclassN

  siRelation [kL, kR] $ \[l, r] -> l .== r
  siRelation [nL, nR] $ \[l, r] -> l .== r
  checkSIMap [kL, nL] [kR, nR]

  -- LHS: x · (y · z), inner contracts N
  yz <- matmul3D y z [rclassN --> nL] [ByRClass rclassB]
  lhs <- matmul3D x yz [rclassK --> kL] [ByRClass rclassB]

  -- RHS: (x · y) · z, inner contracts K
  xy <- matmul3D x y [rclassK --> kR] [ByRClass rclassB]
  rhs <- matmul3D xy z [rclassN --> nR] [ByRClass rclassB]

  rewrite "∀x, y, z. matmul3D(x, matmul3D(y, z)) = matmul3D(matmul3D(x, y), z)" lhs rhs

-- | Rule 2: Scalar linearity (batched)
matmulScalarLinear :: forall a. NumRule a
matmulScalarLinear _ = do
  let w = ("w" :: a)
  [rclassB, rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassB", "rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN
  [sizeB1, sizeB2] <- newMaps ["sizeB1", "sizeB2"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassK --> sizeK, rclassN --> sizeN]

  kL <- newMap "kL" rclassK
  kR <- newMap "kR" rclassK

  xy <- matmul3D x y [rclassK --> kL] [ByRClass rclassB]
  lhs <- smul xy w
  yw <- smul y w
  rhs <- matmul3D x yw [rclassK --> kR] [ByRClass rclassB]

  siRelation [kL, kR] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR]

  rewrite "∀x, y, w. smul(matmul3D(x, y), w) = matmul3D(x, smul(y, w))" lhs rhs

-- | Rule 3: Distributivity over addition (batched)
matmulDistributive :: forall a. NumRule a
matmulDistributive _ = do
  [rclassB, rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassB", "rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  sizeN <- newMap "sizeN" rclassN
  [sizeB1, sizeB2, sizeB3] <- newMaps ["sizeB1", "sizeB2", "sizeB3"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassK --> sizeK, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassB --> sizeB3, rclassK --> sizeK, rclassN --> sizeN]

  yz <- ewadd y z
  kL <- newMap "kL" rclassK
  kR1 <- newMap "kR1" rclassK
  kR2 <- newMap "kR2" rclassK

  lhs <- matmul3D x yz [rclassK --> kL] [ByRClass rclassB]
  xy <- matmul3D x y [rclassK --> kR1] [ByRClass rclassB]
  xz <- matmul3D x z [rclassK --> kR2] [ByRClass rclassB]
  rhs <- ewadd xy xz

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "∀x, y, z. matmul(x, ewadd(y, z)) = ewadd(matmul(x, y), matmul(x, z))" lhs rhs

-- | Rule 4: Right concatenation (batched)
matmulConcatRight :: forall a. NumRule a
matmulConcatRight _ = do
  [rclassB, rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassB", "rclassM", "rclassK", "rclassN"]
  sizeM <- newMap "sizeM" rclassM
  sizeK <- newMap "sizeK" rclassK
  [sizeN1, sizeN2] <- newMaps ["sizeN1", "sizeN2"] rclassN
  [sizeB1, sizeB2, sizeB3] <- newMaps ["sizeB1", "sizeB2", "sizeB3"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassM --> sizeM, rclassK --> sizeK]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassK --> sizeK, rclassN --> sizeN1]
  z <- newTensor @a "z" [rclassB --> sizeB3, rclassK --> sizeK, rclassN --> sizeN2]

  kL1 <- newMap "kL1" rclassK
  kL2 <- newMap "kL2" rclassK
  xy <- matmul3D x y [rclassK --> kL1] [ByRClass rclassB]
  xz <- matmul3D x z [rclassK --> kL2] [ByRClass rclassB]
  lhs <- concat (ByRClass rclassN) xy xz

  yz <- concat (ByRClass rclassN) y z
  kR <- newMap "kR" rclassK
  rhs <- matmul3D x yz [rclassK --> kR] [ByRClass rclassB]

  siRelation [kL1, kR] $ \[l, r] -> l .== r
  siRelation [kL2, kR] $ \[l, r] -> l .== r
  checkSIMap [kL1, kL2] [kR]

  rewrite "concat along N moves through matmul3D(x, ·)" lhs rhs

-- | Rule 5: Concatenation and matrix multiplication (mixed)
-- ∀x, y, z, w. matmul(concat(1, x, z), concat(0, y, w)) = ewadd(matmul(x, y), matmul(z, w))

-- | Rule 5: Mixed concatenation (batched)
matmulConcatMixed :: forall a. NumRule a
matmulConcatMixed _ = do
  [rclassB, rclassM, rclassK, rclassN] <- newSingletonRClasses ["rclassB", "rclassM", "rclassK", "rclassN"]
  [sizeM1, sizeM2] <- newMaps ["sizeM1", "sizeM2"] rclassM
  [sizeK1, sizeK2] <- newMaps ["sizeK1", "sizeK2"] rclassK
  sizeN <- newMap "sizeN" rclassN
  [sizeB1, sizeB2, sizeB3, sizeB4] <- newMaps ["sizeB1", "sizeB2", "sizeB3", "sizeB4"] rclassB

  x <- newTensor @a "x" [rclassB --> sizeB1, rclassM --> sizeM1, rclassK --> sizeK1]
  y <- newTensor @a "y" [rclassB --> sizeB2, rclassK --> sizeK1, rclassN --> sizeN]
  z <- newTensor @a "z" [rclassB --> sizeB3, rclassM --> sizeM2, rclassK --> sizeK2]
  w <- newTensor @a "w" [rclassB --> sizeB4, rclassK --> sizeK2, rclassN --> sizeN]

  -- All batch sizes must match so that B is a proper batch axis
  precondition [sizeB1, sizeB2] $ \[b1, b2] -> b1 .== b2
  precondition [sizeB1, sizeB3] $ \[b1, b3] -> b1 .== b3
  precondition [sizeB1, sizeB4] $ \[b1, b4] -> b1 .== b4
  -- Mixed: equal splits on M and K so SI equality is valid on both branches
  precondition [sizeM1, sizeM2] $ \[m1, m2] -> m1 .== m2
  precondition [sizeK1, sizeK2] $ \[k1, k2] -> k1 .== k2

  xm <- concat (ByRClass rclassM) x z
  yk <- concat (ByRClass rclassK) y w

  -- Contract along K with equal SI maps across sides
  kL <- newMap "kL" rclassK
  kR1 <- newMap "kR1" rclassK
  kR2 <- newMap "kR2" rclassK

  lhs <- matmul3D xm yk [rclassK --> kL] [ByRClass rclassB]
  xy <- matmul3D x y [rclassK --> kR1] [ByRClass rclassB]
  zw <- matmul3D z w [rclassK --> kR2] [ByRClass rclassB]
  rhs <- ewadd xy zw

  siRelation [kL, kR1] $ \[l, r] -> l .== r
  siRelation [kL, kR2] $ \[l, r] -> l .== r
  checkSIMap [kL] [kR1, kR2]

  rewrite "matmul3D(concat_M x z, concat_K y w) ⇒ ewadd(matmul3D(x,y), matmul3D(z,w))" lhs rhs

main :: IO ()
main = do
  printTitle "#################### matmulAssociativity ####################"
  verifyNumDSL matmulAssociativity

  printTitle "#################### matmulScalarLinear #####################"
  verifyNumDSL matmulScalarLinear

  printTitle "#################### matmulDistributive #####################"
  verifyNumDSL matmulDistributive

  printTitle "#################### matmulConcatRight ######################"
  verifyNumDSL matmulConcatRight

-- printTitle "##################### matmulConcatMixed #####################"
-- verifyNumDSL matmulConcatMixed
