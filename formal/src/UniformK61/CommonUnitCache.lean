import UniformK61.CommonFormula

set_option autoImplicit false
namespace UniformK61.CommonUnitCache
open PricingABD.ABLayout CompletionC.NativeMatrices CompletionC.SupportEdges
open UniformK61.Core UniformK61.CommonFormula

abbrev Coordinates (s : Shape) := List ((Fin s.dimension×Fin s.dimension)×(Vertex×Vertex))
def coordinates (l : Layout) (p : Fin 737) : Coordinates (pairTable p).shape :=
  (crossPairs (pairTable p).shape).map fun ab => (ab,label61 l p ab.1.val,label61 l p ab.2.val)
def initial (l : Layout) (t : Types) : List PhysicalUnit :=
  spokes l ++ templates l t ++ freeShape l

def cached (l : Layout) (s : Shape) (head tail : List PhysicalUnit)
    (coords : Coordinates s) (w : Nat) : List PhysicalUnit :=
  let raw := coords.map fun ab =>
    (⟨true,ab.2.1,ab.2.2,matrix s w ab.1.1 ab.1.2⟩ : PhysicalUnit)
  head ++ (if l.profile=.D then raw.mergeSort physicalOrder else raw) ++ tail

theorem cached_eq (l : Layout) (t : Types) (p : Fin 737) (j : Fin (pairTable p).count) :
    cached l (pairTable p).shape (initial l t) (membership l p) (coordinates l p)
      ((pairTable p).representative j) = units l t p j := by
  simp only [cached,coordinates,initial,units,word,rawWord,List.map_map,Function.comp_def]

#print axioms cached_eq
end UniformK61.CommonUnitCache
