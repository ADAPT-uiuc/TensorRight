module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.DSL (newSingletonRClass)
import TensorRight.Internal.DSL.TASO

desugarEnlarge :: forall a. NumRule a
desugarEnlarge _ = do
  rclass <- newSingletonRClass "rclass"
  [n, c, h, w] <- newMaps ["n", "c", "h", "w"] rclass
  tA <- newTensor @a "A" [rclass --> n @@ "N", rclass --> c @@ "C", rclass --> h @@ "H", rclass --> w @@ "W"]
  let kx = ssym "kx" :: SymInteger
  let ky = ssym "ky" :: SymInteger

  -- Prepare shared low padding maps to be used by both LHS and RHS
  hLow <- newNonNegMap "hLow" rclass
  wLow <- newNonNegMap "wLow" rclass

  lhs <- enlarge @a (ByLabel "H" --> h) (ByLabel "W" --> w) hLow wLow ky kx tA

  -- Building the rhs
  kH <- newConstMap "kH" ky rclass
  kW <- newConstMap "kW" kx rclass

  precondition [kH] $ \[k] -> k .>= 0
  precondition [kW] $ \[k] -> k .>= 0

  sH' <- combineMap "sH'" (\[a', k'] -> symIte (a' .>= k') a' k') [h, kH]
  sW' <- combineMap "sW'" (\[a', k'] -> symIte (a' .>= k') a' k') [w, kW]

  dH <- combineMap "dH" (\[m, a'] -> m - a') [sH', h]
  dW <- combineMap "dW" (\[m, a'] -> m - a') [sW', w]

  -- Deterministic split on RHS: low = floor(d/2), high = d - low
  precondition [hLow, dH] $ \[l, d] -> (l + l) .<= d .&& d .<= (l + l + 1)
  hHigh <- combineMap "hHigh" (\[d, l] -> d - l) [dH, hLow]

  precondition [wLow, dW] $ \[l, d] -> (l + l) .<= d .&& d .<= (l + l + 1)
  wHigh <- combineMap "wHigh" (\[d, l] -> d - l) [dW, wLow]

  z <- newConstMap "zero" 0 rclass

  let hRef = ByLabel "H"
  let wRef = ByLabel "W"

  rhs <-
    pad tA (0 :: a) $
      Padding
        { low = [hRef --> hLow, wRef --> wLow],
          interior = [hRef --> z, wRef --> z],
          high = [hRef --> hHigh, wRef --> wHigh]
        }

  rewrite "enlarge(ky, kx, A) ⇒ Pad(A, 0, symmetric(ky on H, kx on W)))" lhs rhs

main :: IO ()
main = do
  printTitle "######################## desugarEnlarge ########################"
  verifyNumDSL desugarEnlarge
