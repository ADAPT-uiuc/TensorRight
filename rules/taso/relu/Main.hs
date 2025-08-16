import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (relu)

rule01 :: forall a. NumRule a -- Verify desugaring
rule01 _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- relu @a tA
  rhs <- clampScalar @a 0 tA posInf
  rewrite "relu(A) ⇒ Clamp(0, A, inf)" lhs rhs

main :: IO ()
main = do
  print "############################## rule01 ##############################"
  verifyNumDSL rule01