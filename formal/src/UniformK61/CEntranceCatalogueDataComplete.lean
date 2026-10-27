import UniformK61.CEntranceCatalogueDataChecks
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace UniformK61.CEntrance.Catalogue
open CompletionC.NativeMatrices CompletionC.CommonSupportNormalization
open PricingIntegration.PairAdmission

theorem header_compatible (h : Fin 21) :
    Compatible (header h).five (header h).leftType (header h).rightType (header h).pair := by
  obtain ⟨hf,hl,hr,hs,ho,_⟩ := header_metadata h
  exact ⟨ho,hf,hl,hr,hs⟩

theorem compatible_eligible {f l r : Bool} {p : Fin 737}
    (hc : Compatible f l r p) : Eligible p := by
  obtain ⟨ho,hf,hl,hr,_⟩ := hc
  refine ⟨hf,?_⟩
  cases l <;> cases r <;> simp_all [Ordered,kindCode]

private theorem kind_injective {a b : Bool} (h : kindCode true a=kindCode true b) : a=b := by
  cases a <;> cases b <;> simp_all [kindCode]

private theorem free_injective {a b : Bool} (h : freeSize a=freeSize b) : a=b := by
  cases a <;> cases b <;> simp_all [freeSize]

theorem compatible_unique {f l r f' l' r' : Bool} {p : Fin 737}
    (h : Compatible f l r p) (h' : Compatible f' l' r' p) :
    f=f' ∧ l=l' ∧ r=r' := by
  obtain ⟨_,_,hl,hr,hf⟩ := h
  obtain ⟨_,_,hl',hr',hf'⟩ := h'
  exact ⟨free_injective (hf.trans hf'.symm),kind_injective (hl.symm.trans hl'),
    kind_injective (hr.symm.trans hr')⟩

/-- Every physically admitted support pair and every one of its native
word representatives occurs in the concrete direct-C catalogue. This is
surjectivity over the entire retained boundary, not a check of listed cases. -/
theorem complete (f l r : Bool) (p : Fin 737) (hc : Compatible f l r p)
    (j : Fin (pairTable p).count) :
    ∃ k : Fin 346, pair k=p ∧ (rep k).val=j.val ∧
      five k=f ∧ leftType k=l ∧ rightType k=r := by
  let h := headerFor p
  have hp : (header h).pair=p := all_eligible_headers p (compatible_eligible hc)
  let jj : Fin (header h).count := ⟨j.val,by rw [(header_bounds h).2,hp];exact j.isLt⟩
  have hr := index_row h jj
  have hs : Compatible (header h).five (header h).leftType (header h).rightType p := by
    simpa only [hp] using header_compatible h
  obtain ⟨hf,hl,hrt⟩ := compatible_unique hs hc
  refine ⟨index h jj,?_,?_,?_,?_,?_⟩
  · change (header (row (index h jj)).header).pair=p
    rw [hr.1];exact hp
  · exact hr.2
  · change (header (row (index h jj)).header).five=f
    rw [hr.1];exact hf
  · change (header (row (index h jj)).header).leftType=l
    rw [hr.1];exact hl
  · change (header (row (index h jj)).header).rightType=r
    rw [hr.1];exact hrt

#print axioms complete
end UniformK61.CEntrance.Catalogue
