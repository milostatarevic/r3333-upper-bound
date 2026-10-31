import UniformK61.UUTemplateTransport
import UniformK60.ReferenceExtension

set_option autoImplicit false
namespace UniformK60.UUSourceFacts
open Ramsey61 UniformK61.Core UniformK61.UUSupportData UniformK61.UUSourceDefs

/-- Reference facts only: the omitted position has no global goodness claim. -/
structure SourceFacts (q : Bool) (p : Pair) (i : Fin 600)
    (c : UnitRestriction.ReferenceColoring) extends
    UniformK61.UUTemplateTransport.StaticHost q c : Prop where
  membership : ∀ v : Vertex, v ≠ 60 → (c v 60 = palette 3 ↔ member p v = true)
  matrix : ∀ a b : Fin (shape p).dimension, a ≠ b →
    c (matrixVertex p a) (matrixVertex p b) =
      palette (CompletionC.NativeMatrices.matrix (shape p) (CompletionC.NativeMatrices.candidate (shape p) i) a b)

end UniformK60.UUSourceFacts
