import CompletionC.NativeWholeReindex
import CompletionC.NativeSupportIndex
set_option autoImplicit false
set_option maxRecDepth 10000
namespace CompletionC.NativeSelectedBlocks
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions PricingC.NativeActionPhysical
open CompletionC.CommonBlocks CompletionC.CommonPairAdmission CompletionC.NativeMatrices
open CompletionC.NativeWholeReindex CompletionC.NativePairRoleFrame CompletionC.NativeShapeCoordinates
open CompletionC.NativeSupportIndex

noncomputable def factorFree (p:Fin 737) (i:Fin 600):Equiv.Perm (Fin (pairTable p).shape.free):=
 (finCongr (selected_factor_sizes p i).1.symm).trans
  ((Classical.choose (free_equiv _ _ (selected_factor_valid p i).1)).trans
    (finCongr (selected_factor_sizes p i).1))

theorem factorFree_val (p:Fin 737) (i:Fin 600) (a:Fin (pairTable p).shape.free):
 (factorFree p i a).val=digit (PricingC.NativeActionFactors.freeCode (selectedFactor p i)) a.val:=by
 exact Classical.choose_spec (free_equiv _ _ (selected_factor_valid p i).1)
  ((finCongr (selected_factor_sizes p i).1.symm) a)

noncomputable def combinedFree {l:Layout} (p:Fin 737) (i:Fin 600)
 (hf:freeSize l=(pairTable p).shape.free) (perm:Equiv.Perm (Fin (pairTable p).shape.free)):
 Equiv.Perm (Fin (freeSize l)):=
 (finCongr hf).trans ((factorFree p i).trans (perm.trans (finCongr hf.symm)))

noncomputable def selectedBlocks {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (i:Fin 600):Blocks c l t:=
 reindexBlocks b (combinedFree p i hf perm) (autoIndex (leftRole p i)) (autoIndex (rightRole p i))

/-- The free component passed to the general physical action theorem.
Only its in-range values are used; the default is immaterial. -/
noncomputable def freeFunction {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (p:Fin 737) (hf:freeSize l=(pairTable p).shape.free)
 (perm:Equiv.Perm (Fin (pairTable p).shape.free)) (n:Nat):Vertex:=
 if h:n<(pairTable p).shape.free then b.free ((finCongr hf.symm) (perm ⟨n,h⟩)) else b.root

#print axioms factorFree_val
#print axioms selectedBlocks
end CompletionC.NativeSelectedBlocks
