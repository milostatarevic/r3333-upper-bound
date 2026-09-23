import CompletionC.NativePairShapes
import CompletionC.NativeFactorBounds
set_option autoImplicit false
namespace CompletionC.NativeMatrices
open PricingC
attribute [local irreducible]
 NativePairActions.selectedCode NativePairActions.selectedIndex NativePairActions.factorAt
 NativePairActions.table NativePairActions.freeSizes NativePairActions.leftSizes NativePairActions.rightSizes
 NativeActionFactors.freeSizesAt NativeActionFactors.leftIdsAt NativeActionFactors.rightIdsAt
 NativeBlockActions.sizes

abbrev pairTable (p:Fin 737):Table:=table (NativePairActions.table p)

theorem selected_factor_sizes (p:Fin 737) (i:Fin 600):
 NativeActionFactors.freeSize (NativePairActions.selectedFactor p i)=(pairTable p).shape.free ∧
 NativeBlockActions.size (NativeActionFactors.left (NativePairActions.selectedFactor p i))=(pairTable p).shape.left ∧
 NativeBlockActions.size (NativeActionFactors.right (NativePairActions.selectedFactor p i))=(pairTable p).shape.right:=by
 have hw:=NativePairActions.selected_factor_witness p i
 unfold NativePairActions.PairWitness at hw
 obtain ⟨_,_,hf,_,_,_,_,hl,hr⟩:=hw
 have hd:=pair_dimensions p
 exact ⟨hf.trans hd.1,hl.trans hd.2.1,hr.trans hd.2.2⟩

theorem selected_factor_dimension (p:Fin 737) (i:Fin 600):
 NativeActionFactors.count (NativePairActions.selectedFactor p i)=(pairTable p).shape.dimension:=by
 obtain ⟨hf,hl,hr⟩:=selected_factor_sizes p i
 unfold NativeActionFactors.count
 rw[hf,hl,hr]
 exact (Shape.dimension_sum _).symm

theorem selected_digit_bound (p:Fin 737) (i:Fin 600) (a:Fin (pairTable p).shape.dimension):
 NativeBlockActions.digit (NativePairActions.selectedCode (NativePairActions.table p) i) a.val <
 (pairTable p).shape.dimension:=by
 have h:=NativeFactorBounds.coordinate_bound (NativePairActions.selectedFactor p i)
  (NativePairActions.selected_factor_valid p i) a.val (by rw[selected_factor_dimension];exact a.isLt)
 rw[NativePairActions.selected_factor_code,selected_factor_dimension] at h
 exact h

/-- The packed coordinate is never truncated by modulo: every native pair
and every matrix witness gives an actual in-range physical coordinate. -/
theorem selected_coordinate_exact (p:Fin 737) (i:Fin 600) (a:Fin (pairTable p).shape.dimension):
 ((pairTable p).coordinate i a).val=
 NativeBlockActions.digit (NativePairActions.selectedCode (NativePairActions.table p) i) a.val:=by
 rw[coordinate_selected, Nat.mod_eq_of_lt (selected_digit_bound p i a)]

theorem selected_coordinate_injective (p:Fin 737) (i:Fin 600):
 Function.Injective ((pairTable p).coordinate i):=by
 intro a b h
 apply Fin.ext
 apply NativeFactorBounds.coordinate_injective (NativePairActions.selectedFactor p i)
  (NativePairActions.selected_factor_valid p i) a.val b.val
  (by rw[selected_factor_dimension];exact a.isLt)
  (by rw[selected_factor_dimension];exact b.isLt)
 rw[NativePairActions.selected_factor_code]
 have he:=congrArg Fin.val h
 rw[selected_coordinate_exact,selected_coordinate_exact] at he
 exact he

noncomputable def selectedEquiv (p:Fin 737) (i:Fin 600):
 Equiv.Perm (Fin (pairTable p).shape.dimension):=
 Equiv.ofBijective ((pairTable p).coordinate i)
  ((Fintype.bijective_iff_injective_and_card _).mpr ⟨selected_coordinate_injective p i,rfl⟩)
#print axioms selected_factor_dimension
#print axioms selected_coordinate_exact
#print axioms selected_coordinate_injective
end CompletionC.NativeMatrices
