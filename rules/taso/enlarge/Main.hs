module Main (main) where

import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (enlarge)

desugarEnlarge :: forall a. NumRule a
desugarEnlarge _ = do
  rclass <- newRClass "rclass"
  [n, c, h, w] <- newMaps ["n", "c", "h", "w"] rclass
  tA <- newTensor @a "A" [rclass --> n @@ "N", rclass --> c @@ "C", rclass --> h @@ "H", rclass --> w @@ "W"]
  let kx = ssym "kx" :: SymInteger
  let ky = ssym "ky" :: SymInteger

  lhs <- enlarge @a (ByLabel "H" --> h) (ByLabel "W" --> w) ky kx tA

  -- Building the rhs
  kH <- newConstMap "kH" ky rclass
  kW <- newConstMap "kW" kx rclass

  sH' <- combineMap "sH'" (\[a', k'] -> symIte (a' .>= k') a' k') [h, kH]
  sW' <- combineMap "sW'" (\[a', k'] -> symIte (a' .>= k') a' k') [w, kW]

  dH <- combineMap "dH" (\[m, a'] -> m - a') [sH', h]
  dW <- combineMap "dW" (\[m, a'] -> m - a') [sW', w]

  hLow <- newNonNegMap "hLow" rclass
  hHigh <- newNonNegMap "hHigh" rclass
  precondition [hLow, hHigh, dH] $ \[l, hv, d] -> l + hv .== d .&& l .<= hv .&& hv .<= l + 1

  wLow <- newNonNegMap "wLow" rclass
  wHigh <- newNonNegMap "wHigh" rclass
  precondition [wLow, wHigh, dW] $ \[l, hv, d] -> l + hv .== d .&& l .<= hv .&& hv .<= l + 1

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