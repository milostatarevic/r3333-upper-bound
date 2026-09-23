import CompletionC.NativeFamilyJoin
set_option autoImplicit false
namespace PricingABD.CommonSuffixCache
open Ramsey61.DenseCounter PricingABD.ABLayout
open CompletionC.NativeMatrices CompletionC.NativeSuffix
open CompletionC.NativeSupportIndex

abbrev Coordinates (s:Shape) := List ((Fin s.dimension × Fin s.dimension) × (Nat × Nat))
def coordinates (l:Layout) (p:Fin 737) : Coordinates (pairTable p).shape :=
 (pairs l p).map fun ab => (ab, label l p ab.1.val, label l p ab.2.val)
def initial (l:Layout) (p:Fin 737) : List Literal :=
 if fullMatrix l then [] else signedUnits l p
def cached (n:Nat) (s:Shape) (head:List Literal) (coords:Coordinates s) (word:Nat) : List Literal :=
 head ++ coords.map fun ab => (true, edgeNat n ab.2.1 ab.2.2 (matrix s word ab.1.1 ab.1.2))

theorem cached_eq (l:Layout) (p:Fin 737) (j:Fin (pairTable p).count) :
 cached (vertexCount l) (pairTable p).shape (initial l p) (coordinates l p)
  ((pairTable p).representative j) = literals l p j := by
 simp only [cached, coordinates, initial, literals, matrixUnits, List.map_map, Function.comp_def]

#print axioms cached_eq
end PricingABD.CommonSuffixCache
