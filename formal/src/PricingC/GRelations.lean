import PricingIntegration.LocalRelations

namespace PricingC.GRelations
open Ramsey61 Ramsey61.CEncodingCore PricingG.Completion72
open PricingIntegration.LocalRelations

def edgeTable : Fin 16 → Fin 16 → Nat := ![![80,80,80,0,80,1,2,3,80,4,5,6,7,8,9,80],![80,80,10,80,11,80,12,13,14,80,15,16,17,18,80,19],![80,10,80,80,20,21,80,22,23,24,80,25,26,80,27,28],![0,80,80,80,29,30,31,80,32,33,34,80,80,35,36,37],![80,11,20,29,80,80,80,38,39,40,41,80,80,42,43,44],![1,80,21,30,80,80,45,80,46,47,80,48,49,80,50,51],![2,12,80,31,80,45,80,80,52,80,53,54,55,56,80,57],![3,13,22,80,38,80,80,80,80,58,59,60,61,62,63,80],![80,14,23,32,39,46,52,80,80,80,80,64,80,65,66,67],![4,80,24,33,40,47,80,58,80,80,68,80,69,80,70,71],![5,15,80,34,41,80,53,59,80,68,80,80,72,73,80,74],![6,16,25,80,80,48,54,60,64,80,80,80,75,76,77,80],![7,17,26,80,80,49,55,61,80,69,72,75,80,80,80,78],![8,18,80,35,42,80,56,62,65,80,73,76,80,80,79,80],![9,80,27,36,43,50,80,63,66,70,80,77,80,79,80,80],![80,19,28,37,44,51,57,80,67,71,74,80,78,80,80,80]]

set_option maxRecDepth 100000 in
private theorem edgeTable_exact : ∀ a b,edgeTable a b=referenceIndex a b := by decide

def fastColor (i : Fin 72) (a b : Fin 16) : Fin 3 :=
 if a=b then 0 else if xorClebsch a b then 0 else if (referenceMask i).testBit (edgeTable a b) then 1 else 2

theorem fastColor_exact (i : Fin 72) (a b : Fin 16) : fastColor i a b=referenceColor i a b := by
 simp only [fastColor,referenceColor,edgeTable_exact]

def rejects (s : ScopeSpec) (i : Fin 72) (p : Fin 10 × Fin 10) : Prop :=
 p.1 < p.2 ∧ ¬ Allows (s.observed p.1 p.2) (s.colors (fastColor i (s.roles p.1) (s.roles p.2)))

instance (s : ScopeSpec) (i : Fin 72) (p : Fin 10 × Fin 10) : Decidable (rejects s i p) :=
 inferInstanceAs (Decidable (p.1 < p.2 ∧ ¬ Allows (s.observed p.1 p.2) (s.colors (fastColor i (s.roles p.1) (s.roles p.2)))))

theorem rejects_not_compatible (s : ScopeSpec) (i : Fin 72) (p : Fin 10 × Fin 10)
 (h : rejects s i p) : ¬ Compatible s i := by
 intro hc
 apply h.2
 simpa only [fastColor_exact,predicted] using hc p.1 p.2 h.1

theorem empty_from_hints (s : ScopeSpec) (hints : Fin 72 → Fin 10 × Fin 10)
 (h : ∀ i,rejects s i (hints i)) : emptyCheck s=true := by
 have hn : rows s=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i hi
  exact rejects_not_compatible s i (hints i) (h i) (of_decide_eq_true (List.mem_filter.mp hi).2)
 simp only [emptyCheck,hn,List.isEmpty_nil]

def forcesOrRejects (s : ScopeSpec) (a b : Fin 10) (q : Color) (i : Fin 72) (p : Fin 10 × Fin 10) : Prop :=
 s.colors (fastColor i (s.roles a) (s.roles b))=q ∨ rejects s i p

instance (s : ScopeSpec) (a b : Fin 10) (q : Color) (i : Fin 72) (p : Fin 10 × Fin 10) : Decidable (forcesOrRejects s a b q i p) :=
 inferInstanceAs (Decidable (s.colors (fastColor i (s.roles a) (s.roles b))=q ∨ rejects s i p))

theorem forced_from_hints (s : ScopeSpec) (a b : Fin 10) (q : Color)
 (hints : Fin 72 → Fin 10 × Fin 10) (h : ∀ i,forcesOrRejects s a b q i (hints i)) : forcedCheck s a b q=true := by
 apply List.all_eq_true.mpr
 intro i hi
 have hc : Compatible s i := of_decide_eq_true (List.mem_filter.mp hi).2
 have hf := (h i).resolve_right (fun hr => rejects_not_compatible s i (hints i) hr hc)
 exact beq_iff_eq.mpr (by simpa only [fastColor_exact,predicted] using hf)

#print axioms empty_from_hints
#print axioms forced_from_hints
end PricingC.GRelations
