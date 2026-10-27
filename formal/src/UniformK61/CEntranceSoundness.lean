import UniformK61.CEntranceMembership
set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter
open PricingIntegration.BActualFrame PricingIntegration.PairAdmission
open CompletionC.NativeMatrices CompletionC.SupportEdges CompletionC.NativeFreeGeometry
open Formula
variable {c : Host} {five lt rt : Bool}

theorem ordered_ne {n : Nat} (ab : Fin n×Fin n)
    (h : ab∈PricingABD.ABGeometry.orderedPairs n) : ab.1≠ab.2 := by
  simp only [PricingABD.ABGeometry.orderedPairs,List.mem_flatMap,List.mem_map] at h
  obtain ⟨a,_,d,hd,rfl⟩ := h
  exact ne_of_lt (by simpa using (List.mem_filter.mp hd).2)

theorem templates_match (b : Blocks c five lt rt) :
    Core.UnitsMatch (coloring b) (templates lt rt) := by
  intro u hu
  rcases List.mem_append.mp hu with h|h
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he
      apply ordered_ne ab hab
      apply Fin.ext
      have he' := congrArg Fin.val he
      simp only [leftVertex,Fin.val_mk] at he'
      omega
    · change c (fullMap b (leftVertex ab.1)) (fullMap b (leftVertex ab.2)) = _
      rw [fullMap_left,fullMap_left,b.left.map_color _ _ (ordered_ne ab hab),b.left_palette]
      rfl
  · obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp h
    refine ⟨?_,?_⟩
    · intro he
      apply ordered_ne ab hab
      apply Fin.ext
      have he' := congrArg Fin.val he
      simp only [rightVertex,Fin.val_mk] at he'
      omega
    · change c (fullMap b (rightVertex ab.1)) (fullMap b (rightVertex ab.2)) = _
      rw [fullMap_right,fullMap_right,b.right.map_color _ _ (ordered_ne ab hab),b.right_palette]
      rfl

theorem supportVertex_free {c d : Host} {five lt rt lt' rt' : Bool}
    (b : Blocks c five lt rt) (s : Shape) (hf : freeSize five=s.free)
    (p : Fin 737) (hp : retained p=sourceRecord b s) (z : Blocks d five lt' rt')
    (a : Fin (freeSize five)) :
    supportVertex b s hf p hp z (freeIndex s ((finCongr hf) a))=z.free a := by
  have ha : a.val<s.free := by rw [←hf];exact a.isLt
  simp only [supportVertex,freeIndex,finCongr_apply_coe,dif_pos ha]

theorem freePattern_eq (s : Shape) (hf : freeSize five=s.free)
    (a d : Fin (freeSize five)) :
    freePattern s ((finCongr hf) a) ((finCongr hf) d)=Formula.freeColor five a d := by
  have he : (s.free=5) ↔ five=true := by rw [←hf];cases five <;> decide
  simp only [freePattern,Formula.freeColor,finCongr_apply_coe,he]

theorem free_match (b z : Blocks c five lt rt) (s : Shape) (hf : freeSize five=s.free)
    (p : Fin 737) (hp : retained p=sourceRecord b s) (w : Nat)
    (hmat : ∀a d : Fin s.dimension,a≠d →
      c (supportVertex b s hf p hp z a) (supportVertex b s hf p hp z d)=palette (matrix s w a d)) :
    Core.UnitsMatch (coloring z) (freeShape five) := by
  intro u hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
  have had := ordered_ne ab hab
  refine ⟨?_,?_⟩
  · intro he
    apply had
    apply Fin.ext
    have he' := congrArg Fin.val he
    simp only [lowVertex,Fin.val_mk] at he'
    omega
  · have hn : freeIndex s ((finCongr hf) ab.1)≠freeIndex s ((finCongr hf) ab.2) := by
      intro he
      apply had
      exact Fin.ext (congrArg (fun x : Fin s.dimension => x.val) he)
    have hm := hmat _ _ hn
    rw [supportVertex_free,supportVertex_free,matrix_free _ _ _ _ ((finCongr hf).injective.ne had),freePattern_eq s hf] at hm
    change c (fullMap z (lowVertex _)) (fullMap z (lowVertex _)) = _
    simpa only [fullMap_low,low_initial] using hm

theorem word_match (b z : Blocks c five lt rt) (p : Fin 737)
    (hf : freeSize five=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape) (j : Fin (pairTable p).count)
    (hmat : ∀a d : Fin (pairTable p).shape.dimension,a≠d →
      c (supportVertex b (pairTable p).shape hf p hp z a)
        (supportVertex b (pairTable p).shape hf p hp z d)=
      palette (matrix (pairTable p).shape ((pairTable p).representative j) a d)) :
    Core.UnitsMatch (coloring z) (word p j) := by
  intro u hu
  obtain ⟨ab,hab,rfl⟩ := List.mem_map.mp hu
  have hn : ab.1≠ab.2 := by
    rcases List.mem_append.mp hab with h|h
    · rcases List.mem_append.mp h with h|h
      · exact product_ne _ 0 1 (by decide) ab h
      · exact product_ne _ 0 2 (by decide) ab h
    · exact product_ne _ 1 2 (by decide) ab h
  change Formula.label61 p ab.1.val≠Formula.label61 p ab.2.val ∧ _
  rw [label61_eq b p hf hp ab.1,label61_eq b p hf hp ab.2]
  refine ⟨(supportIndex_injective b (pairTable p).shape hf p hp).ne hn,?_⟩
  change c (fullMap z (supportIndex b (pairTable p).shape hf p hp ab.1))
    (fullMap z (supportIndex b (pairTable p).shape hf p hp ab.2))=_
  simpa only [supportIndex_physical] using hmat _ _ hn

/-- Every admitted support/word representative is realized on the complete
original host, including the omitted free vertices and the untemplated
marked root cell. -/
theorem admitted_pair_satisfiable (b : Blocks c five lt rt) (hc : NoMonochromaticTriangle c)
    (p : Fin 737) (hf : freeSize five=(pairTable p).shape.free)
    (hp : retained p=sourceRecord b (pairTable p).shape) :
    ∃ j : Fin (pairTable p).count, ∃ w : Valuation,
      FormulaSat w (Formula.formula five lt rt p j) := by
  obtain ⟨perm,i,hmat⟩ := native_representative b hc p hf hp
  let z := selectedBlocks b p hf perm i
  have hl := left_native_membership b p hf hp perm i
  have hr := right_native_membership b p hf hp perm i
  have hu : Core.UnitsMatch (coloring z) (units five lt rt p ((pairTable p).target i)) := by
    intro u hu
    simp only [units,List.mem_append] at hu
    rcases hu with (((h|h)|h)|h)|h
    · exact spokes_match z u h
    · exact templates_match z u h
    · exact free_match b z (pairTable p).shape hf p hp _ hmat u h
    · exact word_match b z p hf hp _ hmat u h
    · exact membership_match z hc p hl hr u h
  exact ⟨(pairTable p).target i,Core.physicalValuation (coloring z),
    Core.coloring_satisfies_formula (coloring z) (coloring_good z hc) _ hu⟩

#print axioms admitted_pair_satisfiable
end UniformK61.CEntrance
