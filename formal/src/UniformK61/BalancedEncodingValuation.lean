import UniformK61.BalancedEncodingPhysical

set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedEncodingData

/-- The disjoint physical, support-selector and local-embedding ranges. -/
def extension {c : Host} {o : Owner} (old : Valuation) (ws : Witnesses c o) (n : Nat) : Bool :=
  if n < 7321 then old n else
  if n < 7833 then
    let s : Scope := ⟨((n-7321)/16)%32,Nat.mod_lt _ (by decide)⟩
    let i : Fin 16 := ⟨(n-7321)%16,Nat.mod_lt _ (by decide)⟩
    decide (i=ws.pattern s)
  else
    let s : Scope := ⟨((n-7833)/182)%32,Nat.mod_lt _ (by decide)⟩
    let offset := (n-7833)%182
    if offset < 176 then
      let m : Fin 16 := ⟨(offset/11)%16,Nat.mod_lt _ (by decide)⟩
      let t : Fin 11 := ⟨offset%11,Nat.mod_lt _ (by decide)⟩
      decide ((ws.scopes s).role m = some t)
    else
      let k : Fin 6 := ⟨(offset-176)%6,Nat.mod_lt _ (by decide)⟩
      decide (k=(ws.scopes s).state)

theorem extension_below {c : Host} {o : Owner} (old : Valuation) (ws : Witnesses c o) (n : Nat) (h : n < 7321) :
    extension old ws n = old n := by simp [extension,h]

theorem extension_pattern {c : Host} {o : Owner} (old : Valuation) (ws : Witnesses c o) (s : Scope) (i : Fin 16) :
    extension old ws (patternAtom s i) = decide (i=ws.pattern s) := by
  have hs := s.isLt; have hi := i.isLt
  have hb0 : ¬patternAtom s i < 7321 := by unfold patternAtom; omega
  have hb1 : patternAtom s i < 7833 := by unfold patternAtom; omega
  have hds : ((patternAtom s i-7321)/16)%32 = s.val := by unfold patternAtom; omega
  have hdi : (patternAtom s i-7321)%16 = i.val := by unfold patternAtom; omega
  simp only [extension,hb0,if_false,hb1,if_true,hds,hdi]

theorem extension_role {c : Host} {o : Owner} (old : Valuation) (ws : Witnesses c o) (s : Scope) :
    RoleMatches (extension old ws) (ws.scopes s) := by
  intro m t
  have hs := s.isLt; have hm := m.isLt; have ht := t.isLt
  have hb0 : ¬roleAtom s m t < 7321 := by unfold roleAtom firstAtom; omega
  have hb1 : ¬roleAtom s m t < 7833 := by unfold roleAtom firstAtom; omega
  have hmt : 11*m.val+t.val < 182 := by omega
  have hsub : roleAtom s m t-7833 = 182*s.val+(11*m.val+t.val) := by unfold roleAtom firstAtom; omega
  have hdiv : (roleAtom s m t-7833)/182 = s.val := by rw [hsub]; omega
  have hds : ((roleAtom s m t-7833)/182)%32 = s.val := by rw [hdiv]; exact Nat.mod_eq_of_lt hs
  have hdo : (roleAtom s m t-7833)%182 = 11*m.val+t.val := by unfold roleAtom firstAtom; omega
  have hb2 : 11*m.val+t.val < 176 := by omega
  have hdm : ((11*m.val+t.val)/11)%16 = m.val := by omega
  have hdt : (11*m.val+t.val)%11 = t.val := by omega
  simp only [extension,hb0,if_false,hb1,hds,hdo,hb2,if_true,hdm,hdt]
  have hsfin : (⟨((roleAtom s m t-7833)/182)%32,Nat.mod_lt _ (by decide)⟩ : Scope) = s := Fin.ext hds
  rw [hsfin]

theorem extension_state {c : Host} {o : Owner} (old : Valuation) (ws : Witnesses c o) (s : Scope) :
    StateMatches (extension old ws) (ws.scopes s) := by
  intro k
  have hs := s.isLt; have hk := k.isLt
  have hb0 : ¬stateAtom s k < 7321 := by unfold stateAtom firstAtom; omega
  have hb1 : ¬stateAtom s k < 7833 := by unfold stateAtom firstAtom; omega
  have hds : ((stateAtom s k-7833)/182)%32 = s.val := by unfold stateAtom firstAtom; omega
  have hdo : (stateAtom s k-7833)%182 = 176+k.val := by unfold stateAtom firstAtom; omega
  have hb2 : ¬176+k.val < 176 := by omega
  have hdk : (176+k.val-176)%6 = k.val := by omega
  simp only [extension,hb0,if_false,hb1,hds,hdo,hb2,hdk]
  have hsfin : (⟨((stateAtom s k-7833)/182)%32,Nat.mod_lt _ (by decide)⟩ : Scope) = s := Fin.ext hds
  rw [hsfin]

theorem base_bound : ∀ clause ∈ Core.baseCNF, ∀ lit ∈ clause, lit.2 < 7321 := by
  intro clause hc lit hl
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨uv,huv,hc⟩ := List.mem_flatMap.mp hc
    rcases uv with ⟨u,v⟩
    have huv' : u < v := by simpa [orderedPairs] using huv
    rcases List.mem_append.mp hc with hc | hc
    · simp only [List.mem_singleton] at hc; subst clause
      obtain ⟨q,_,rfl⟩ := List.mem_map.mp hl
      exact (orderedEdgeVar_bounds u v q huv').2
    · obtain ⟨q,_,hc⟩ := List.mem_flatMap.mp hc
      obtain ⟨r,_,rfl⟩ := List.mem_map.mp hc
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases hl with rfl | rfl
      · exact (orderedEdgeVar_bounds u v q huv').2
      · exact (orderedEdgeVar_bounds u v r huv').2
  · obtain ⟨u,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨v,hv,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨w,hw,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hc
    have huv : u < v := by simpa using (List.mem_filter.mp hv).2
    have hvw : v < w := by simpa using (List.mem_filter.mp hw).2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact (orderedEdgeVar_bounds u v q huv).2
    · exact (orderedEdgeVar_bounds u w q (lt_trans huv hvw)).2
    · exact (orderedEdgeVar_bounds v w q hvw).2

/-- Exact full-host formula satisfaction, conditional only on the finite
coordinate witnesses constructed from actual visible neighborhoods. -/
theorem host_witness_satisfies (c : Host) (hc : NoMonochromaticTriangle c) (o : Owner)
    (hn : Normalized c o.left o.right) (ws : Witnesses c o) :
    ∃ v : Valuation, FormulaSat v (formula o) ∧
      ∀ a, a < 7321 → v a = physicalValuation c a := by
  let old := physicalValuation c
  let v := extension old ws
  have hphysical (a : Nat) (ha : a < 7321) : v a = physicalValuation c a := by
    exact extension_below old ws a ha
  have hp : PhysicalMatches v c := by
    intro a b hab q
    exact (hphysical _ (edgeVar_bounds a b q hab).2).trans (physical_matches c a b hab q)
  refine ⟨v,?_,hphysical⟩
  simp only [formula,extra,formulaSat_append]
  refine ⟨?_,⟨⟨⟨⟨⟨spokes_sat hp hn.spokes,templates_sat hp hn⟩,grid_sat hp⟩,mixed_sat hp hc hn⟩,?_⟩,?_⟩⟩
  · exact formulaSat_congr_below (physicalValuation c) v _ 7321 base_bound hphysical (Core.coloring_satisfies_base c hc)
  · exact sat_flatMap v _ _ fun s _ => selectors_sat hp ws s (extension_pattern old ws s)
  · exact sat_flatMap v _ _ fun s _ => embedding_sat v (ws.scopes s) hp (extension_role old ws s) (extension_state old ws s)

#print axioms host_witness_satisfies
end UniformK61.BalancedEncoding
