import PricingABD.ABFastFold
import PricingG.MultiSparseCounter
import PricingG.MultiSparseAllocation

set_option autoImplicit false
namespace PricingABD.ABProgram
open Ramsey61 Ramsey61.DenseCounter
open PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABCommands PricingABD.ABScheduleTypes
open PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold PricingIntegration.ThresholdCompile

structure Program (l : Layout) (requests counters : Nat) where
  kind : Fin requests → Kind l
  inputs : Fin counters → List Lit
  height : Fin counters → Nat
  start : Fin counters → Nat
  reference : Fin requests → Option (Fin counters)
  fresh : Fin requests → Bool

def bound {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) : Bound := command l (p.kind i)
def target {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) : Nat :=
  (bound p i).limit + if (bound p i).upper then 1 else 0

def FoldOK {l : Layout} {M N : Nat} (p : Program l M N) (t : Types) (i : Fin M) : Prop :=
  match p.reference i with
  | none => target p i≤ABFastFold.fixed l t (p.kind i)
  | some j => ABFastFold.inputs l (p.kind i)=p.inputs j ∧
      target p i-ABFastFold.fixed l t (p.kind i)=p.height j ∧
      0<p.height j ∧ p.height j≤(p.inputs j).length
instance {l : Layout} {M N : Nat} (p : Program l M N) (t : Types) (i : Fin M) : Decidable (FoldOK p t i) := by
  unfold FoldOK;cases p.reference i <;> infer_instance

def InputOK {l : Layout} {M N : Nat} (p : Program l M N) (j : Fin N) : Prop :=
  (p.inputs j).all (fun x=>decide (x.2<primaryLimit l))=true
instance {l : Layout} {M N : Nat} (p : Program l M N) (j : Fin N) : Decidable (InputOK p j) := inferInstanceAs (Decidable (_=true))

def chosenTop {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) : Signal :=
  match p.reference i with
  | none => .constant true
  | some j => PricingIntegration.SparseCounter.threshold (p.start j) (p.height j) (p.inputs j).length (p.height j)
def counterFormula {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) : CNF :=
  match p.reference i with
  | none => []
  | some j => if p.fresh i then normalizeFormula (PricingIntegration.SparseCounter.signals (p.inputs j) (p.start j) (p.height j)) else []
def assertionFormula {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) : CNF :=
  normalizeFormula [boundClause (bound p i).gate (boundSignal (bound p i).upper (chosenTop p i))]
def formula {l : Layout} {M N : Nat} (p : Program l M N) : CNF :=
  (List.finRange M).flatMap (fun i=>counterFormula p i++assertionFormula p i)

theorem chosenTop_correct {l : Layout} {M N : Nat} (p : Program l M N)
    (s t : Types) (hst : SameSchedule l t s) (checked : ∀i,FoldOK p s i)
    (v w : Valuation) (hk : Sound v (ABKnown.known l t))
    (hs : ∀j,Holds w (PricingIntegration.SparseCounter.threshold (p.start j) (p.height j) (p.inputs j).length (p.height j)) ↔
      p.height j≤count v (p.inputs j)) (i : Fin M) :
    Holds w (chosenTop p i) ↔ target p i≤count v (bound p i).xs := by
  have hf:=folded_threshold_iff v (ABKnown.known l t) hk (bound p i).xs (target p i)
  have he : trueFixed (ABKnown.known l t) (bound p i).xs=ABFastFold.fixed l s (p.kind i) :=
    (command_fixed_same t s hst (p.kind i)).trans (ABFastFold.fixed_correct l s (p.kind i)).symm
  have hx : unknown (ABKnown.known l t) (bound p i).xs=ABFastFold.inputs l (p.kind i) :=
    (ABFastFold.inputs_correct l t (p.kind i)).symm
  rw [he,hx] at hf
  have hh:=checked i
  unfold FoldOK at hh
  split at hh
  · rename_i hr
    simp only [chosenTop,hr,Holds]
    rw [hf]
    simp only [hh,if_true]
  · rename_i j hr
    have hp : ¬target p i≤ABFastFold.fixed l s (p.kind i) := by omega
    have hn : ¬(p.inputs j).length<p.height j := by omega
    simp only [chosenTop,hr]
    rw [hs,hf]
    simp only [hp,if_false,hh.1,hh.2.1,hn]

theorem gates_below {l : Layout} {M N : Nat} (p : Program l M N) (i : Fin M) :
    ∀g∈(bound p i).gate,g<primaryLimit l := by
  unfold bound
  cases p.kind i <;> simp [command,high,primaryLimit] <;> omega

theorem assertion_sat {c : Ramsey61.Host} {l : Layout} {M N : Nat} (p : Program l M N)
    (f : Frame c l) (hc : NoMonochromaticTriangle c) (w : Valuation)
    (hw : ∀a<primaryLimit l,w a=primary f a)
    (ht : ∀i,Holds w (chosenTop p i) ↔ target p i≤count (primary f) (bound p i).xs)
    (i : Fin M) : FormulaSat w (assertionFormula p i) := by
  apply normalizeFormula_sound
  simp only [assertionFormula,SignalFormulaSat,List.mem_singleton,forall_eq]
  have hv : Holds w (boundSignal (bound p i).upper (chosenTop p i)) ↔
      if (bound p i).upper then count (primary f) (bound p i).xs≤(bound p i).limit else (bound p i).limit≤count (primary f) (bound p i).xs := by
    cases hu:(bound p i).upper
    · simpa [boundSignal,hu,target] using ht i
    · simp only [boundSignal,hu,if_true,holds_negate]
      rw [ht i]
      simp only [target,hu,if_true]
      omega
  have hb:=physical_command f hc (p.kind i)
  change boundHolds (primary f) (bound p i).xs (bound p i).limit (bound p i).upper (bound p i).gate at hb
  cases he:(bound p i).gate with
  | none =>
    have hh:=hb (by simp [he])
    exact ⟨_,by simp [boundClause,he],hv.mpr hh⟩
  | some g =>
    by_cases hp:primary f g=true
    · have hh:=hb (by simpa [he] using hp)
      exact ⟨_,by simp [boundClause,he],hv.mpr hh⟩
    · refine ⟨.literal (false,g),by simp [boundClause,he],?_⟩
      change w g=false
      rw [hw g (gates_below p i g (by simp [he]))]
      exact Bool.eq_false_iff.mpr hp

theorem satisfying_extension {c : Ramsey61.Host} {l : Layout} {M N : Nat}
    (p : Program l M N) (s t : Types) (hst : SameSchedule l t s)
    (checkedFold : ∀i,FoldOK p s i) (checkedInput : ∀j,InputOK p j)
    (checkedStart : ∀j,p.start j=PricingIntegration.MultiSparseCounter.start (primaryLimit l)
      (PricingIntegration.MultiSparseCounter.size p.inputs p.height) j)
    (f : Frame c l) (hc : NoMonochromaticTriangle c) (hg : Geometry t f) :
    ∃w:Valuation,(∀a<primaryLimit l,w a=primary f a) ∧ FormulaSat w (formula p) := by
  have hb : ∀j,∀x∈p.inputs j,x.2<primaryLimit l := by
    intro j x hx
    exact of_decide_eq_true ((List.all_eq_true.mp (checkedInput j)) x hx)
  obtain ⟨w,hw,hdefs,ht⟩:=PricingIntegration.MultiSparseCounter.simultaneous_satisfying_extension
    (primary f) (primaryLimit l) p.inputs p.height hb
  have hd : ∀j,FormulaSat w (normalizeFormula (PricingIntegration.SparseCounter.signals (p.inputs j) (p.start j) (p.height j))) := by
    intro j;rw [checkedStart];exact hdefs j
  have htop : ∀j,Holds w (PricingIntegration.SparseCounter.threshold (p.start j) (p.height j) (p.inputs j).length (p.height j)) ↔
      p.height j≤count (primary f) (p.inputs j) := by
    intro j;rw [checkedStart]
    simpa [PricingIntegration.SparseCounter.prefixCountSigned] using ht j (p.inputs j).length (le_refl _) (p.height j) (le_refl _)
  have hchosen:=chosenTop_correct p s t hst checkedFold (primary f) w (ABKnown.known_sound f hg) htop
  refine ⟨w,hw,?_⟩
  intro cl hcl
  obtain ⟨i,_,hcl⟩:=List.mem_flatMap.mp hcl
  rcases List.mem_append.mp hcl with hdcl|hacl
  · cases hr:p.reference i with
    | none => simp [counterFormula,hr] at hdcl
    | some j =>
      by_cases hf:p.fresh i=true
      · apply hd j cl
        simpa [counterFormula,hr,hf] using hdcl
      · simp [counterFormula,hr,hf] at hdcl
  · exact assertion_sat p f hc w hw hchosen i cl hacl

#print axioms satisfying_extension
end PricingABD.ABProgram
