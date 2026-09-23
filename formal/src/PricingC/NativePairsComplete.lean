import PricingC.NativeFactorsComplete
import PricingC.NativeSelectedChoices
import PricingC.NativePairActions0
import PricingC.NativePairActions1
import PricingC.NativePairActions2
import PricingC.NativePairActions3
import PricingC.NativeActionPhysical
namespace PricingC.NativePairActions
attribute [local irreducible] PairWitness choiceCount choice table factorAt selectedCode selectedIndex
set_option maxHeartbeats 0

theorem all_pair_witness (p:Fin 737) (j:Nat) (hj:j<choiceCount (table p)):PairWitness p j:=by
 have hall:(List.range (choiceCount (table p))).all (fun j=>decide (PairWitness p j))=true:=by
  by_cases h0:p.val<200
  · simpa only [Nat.zero_add] using pairs0 ⟨p.val,h0⟩
  by_cases h1:p.val<400
  · let k:Fin 200:=⟨p.val-200,by omega⟩
    have h:(⟨200+k.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[k];omega
    rw[←h];exact pairs1 k
  by_cases h2:p.val<600
  · let k:Fin 200:=⟨p.val-400,by omega⟩
    have h:(⟨400+k.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[k];omega
    rw[←h];exact pairs2 k
  · let k:Fin 137:=⟨p.val-600,by omega⟩
    have h:(⟨600+k.val,by omega⟩:Fin 737)=p:=by apply Fin.ext;dsimp[k];omega
    rw[←h];exact pairs3 k
 exact of_decide_eq_true (List.all_eq_true.mp hall j (List.mem_range.mpr hj))

def selectedFactor (p:Fin 737) (i:Fin 600):Fin 27280:=factorAt p (selectedIndex (table p) i)

theorem selected_factor_valid (p:Fin 737) (i:Fin 600):
 NativeActionFactors.Valid (selectedFactor p i):=NativeFactorGeometry.all_factor_valid _

theorem selected_factor_witness (p:Fin 737) (i:Fin 600):
 PairWitness p (selectedIndex (table p) i):=
 all_pair_witness p _ (selected_choice_correct (table p) i).1

theorem selected_factor_code (p:Fin 737) (i:Fin 600):
 NativeActionFactors.coordinateCode (selectedFactor p i)=selectedCode (table p) i:=by
 have hw:=selected_factor_witness p i
 unfold PairWitness at hw
 have he : NativeActionFactors.coordinateCode (selectedFactor p i)=choice (table p) (selectedIndex (table p) i) := by
  rcases hw with ⟨_,he,_,_,_,_,_,_,_⟩
  exact he
 exact he.trans (selected_choice_correct (table p) i).2

/-- All737 retained pairs and all600 initial words use an admissible whole
physical action with exactly the matrix normalizer's packed coordinates. -/
theorem all_selected_physical_transport {V C:Type} (p:Fin 737) (i:Fin 600)
 (free:Nat→V)
 (l:Fin (NativeBlockAutomorphisms.order (NativeBlockActions.kind (NativeActionFactors.left (selectedFactor p i))))↪V)
 (r:Fin (NativeBlockAutomorphisms.order (NativeBlockActions.kind (NativeActionFactors.right (selectedFactor p i))))↪V)
 (host:V→V→C) (a b:Fin 15)
 (ha:a.val<NativeActionFactors.count (selectedFactor p i))
 (hb:b.val<NativeActionFactors.count (selectedFactor p i)):
 host (NativeActionPhysical.after (selectedFactor p i) free l r a.val)
      (NativeActionPhysical.after (selectedFactor p i) free l r b.val)=
 host (NativeActionPhysical.before (selectedFactor p i) free l r
        (NativeBlockActions.digit (selectedCode (table p) i) a.val))
      (NativeActionPhysical.before (selectedFactor p i) free l r
        (NativeBlockActions.digit (selectedCode (table p) i) b.val)):=by
 have h:=NativeActionPhysical.physical_edge_transport (selectedFactor p i)
  (selected_factor_valid p i) free l r host a b ha hb
 rw[selected_factor_code] at h
 exact h
#print axioms all_pair_witness
#print axioms selected_factor_code
#print axioms all_selected_physical_transport
end PricingC.NativePairActions
