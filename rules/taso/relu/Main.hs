import Grisette hiding ((-->))
import TensorRight
import TensorRight.Internal.DSL.TASO (relu)

desugar :: forall a. NumRule a -- Verify desugaring
desugar _ = do
  rclass <- newRClass "rclass"
  map <- newMap "map" rclass
  tA <- newTensor @a "A" [rclass --> map]
  lhs <- relu @a tA
  rhs <- clampScalar @a 0 tA posInf
  rewrite "relu(A) ⇒ Clamp(0, A, inf)" lhs rhs

main :: IO ()
main = do
  printTitle "############################## desugar ##############################"
  verifyNumDSL desugar