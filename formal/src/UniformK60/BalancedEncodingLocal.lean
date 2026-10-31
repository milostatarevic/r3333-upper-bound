import UniformK60.BalancedEncodingDefs

/-! Soundness of the six-table pentagon encoding for either fifteen or
sixteen candidate physical members. -/
set_option autoImplicit false
namespace UniformK60.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK61.BalancedEncodingData
open UniformK61.BalancedEncoding (mem_pairs sat_map sat_flatMap oneHot_sat)

def PhysicalMatches (v : Valuation) (c : Host) : Prop :=
  ∀ u w : Vertex, u ≠ w → ∀ q, v (edgeVar u w q) = decide (c u w = palette q)

def RoleMatches {n : Nat} {c : Host} {g : Geometry n} (v : Valuation) (w : LocalWitness c g) : Prop :=
  ∀ m t, v (g.roleAtom m t) = decide (w.role m = some t)
def StateMatches {n : Nat} {c : Host} {g : Geometry n} (v : Valuation) (w : LocalWitness c g) : Prop :=
  ∀ k, v (g.stateAtom k) = decide (k = w.state)


theorem active_matches {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hp : PhysicalMatches v c) (m : Fin n) :
    v (activeAtom g m) = (w.role m).isSome := by
  rw [activeAtom,hp _ _ (g.center_ne m),w.active]

theorem domains_sat {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hp : PhysicalMatches v c) (hr : RoleMatches v w) (m : Fin n) :
    FormulaSat v (domains g m) := by
  simp only [domains,formulaSat_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro clause hc
    simp only [List.mem_singleton] at hc; subst clause
    cases hh : w.role m with
    | none => exact ⟨negative (activeAtom g m),by simp,by simp [negative,active_matches v w hp,hh]⟩
    | some t =>
      exact ⟨positive (g.roleAtom m t),by simp,by simp [positive,hr m t,hh]⟩
  · apply sat_map
    intro t _
    by_cases hh : w.role m = some t
    · exact ⟨positive (activeAtom g m),by simp,by simp [positive,active_matches v w hp,hh]⟩
    · exact ⟨negative (g.roleAtom m t),by simp,by simp [negative,hr m t,hh]⟩
  · apply sat_map
    rintro ⟨t,u⟩ hm
    have htu : t ≠ u := ne_of_lt (mem_pairs.mp hm)
    by_cases hh : w.role m = some t
    · have hu : w.role m ≠ some u := by simpa [hh] using htu
      exact ⟨negative (g.roleAtom m u),by simp,by simp [negative,hr m u,hu]⟩
    · exact ⟨negative (g.roleAtom m t),by simp,by simp [negative,hr m t,hh]⟩

theorem injection_sat {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hr : RoleMatches v w) (a b : Fin n) (hab : a ≠ b) (t : Fin 11) :
    ClauseSat v [negative (g.roleAtom a t),negative (g.roleAtom b t)] := by
  by_cases hh : w.role a = some t
  · have hb : w.role b ≠ some t := fun hb => hab (w.injective a b t hh hb)
    exact ⟨negative (g.roleAtom b t),by simp,by simp [negative,hr b t,hb]⟩
  · exact ⟨negative (g.roleAtom a t),by simp,by simp [negative,hr a t,hh]⟩

theorem anchor_sat {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) (m : Fin n) (t : Fin 11) (a : Fin 5) :
    FormulaSat v (anchorClauses g m t a) := by
  have hphys (q : Color) : v (anchorAtom g m a q) = decide (c (g.anchor a) (g.member m) = palette q) :=
    hp _ _ (g.anchor_ne a m) q
  unfold anchorClauses
  split_ifs with hc
  · intro clause hm
    simp only [List.mem_singleton] at hm; subst clause
    by_cases hh : w.role m = some t
    · have hconst := of_decide_eq_true hc
      have he := w.anchors m t hh a
      rw [hconst w.state] at he
      exact ⟨positive (anchorAtom g m a (statePhysicalColor g 0 a t)),by simp,by simp [positive,hphys,he]⟩
    · exact ⟨negative (g.roleAtom m t),by simp,by simp [negative,hr m t,hh]⟩
  · rw [formulaSat_append]
    constructor
    · apply sat_map
      intro q hq
      have hnot : ¬ ∃ k : Fin 6, statePhysicalColor g k a t = foreign (g.scopeColor) q := by
        simpa [possibleAnchor] using (List.mem_filter.mp hq).2
      by_cases hh : w.role m = some t
      · have he := w.anchors m t hh a
        have hne : c (g.anchor a) (g.member m) ≠ palette (foreign (g.scopeColor) q) := by
          rw [he]
          intro hh
          exact hnot ⟨w.state,palette_injective hh⟩
        exact ⟨negative (anchorAtom g m a (foreign (g.scopeColor) q)),by simp,by simp [negative,hphys,hne]⟩
      · exact ⟨negative (g.roleAtom m t),by simp,by simp [negative,hr m t,hh]⟩
    · apply sat_map
      intro k _
      by_cases hh : w.role m = some t
      · by_cases hk : k = w.state
        · subst k
          exact ⟨positive (anchorAtom g m a (statePhysicalColor g w.state a t)),by simp,
            by simp [positive,hphys,w.anchors m t hh a]⟩
        · exact ⟨negative (g.stateAtom k),by simp,by simp [negative,hs k,hk]⟩
      · exact ⟨negative (g.roleAtom m t),by simp,by simp [negative,hr m t,hh]⟩

theorem member_support_mem {n : Nat} {c : Host} {g : Geometry n} (w : LocalWitness c g)
    (a b : Fin n) (hab : a ≠ b) (t u : Fin 11) (ha : w.role a = some t) (hb : w.role b = some u) :
    u ∈ memberSupport w.state (g.memberColor a b) t := by
  have hut : u ≠ t := by
    intro h; subst u; exact hab (w.injective a b t ha hb)
  simp [memberSupport,hut,w.members a b t u hab ha hb]

theorem member_sat {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) (a b : Fin n) (hab : a ≠ b) (t : Fin 11) :
    FormulaSat v (memberClauses g a b t) := by
  simp only [memberClauses]
  split_ifs with hc
  · intro clause hm
    simp only [List.mem_singleton] at hm; subst clause
    by_cases ha : w.role a = some t
    · cases hb : w.role b with
      | none => exact ⟨negative (activeAtom g b),by simp,by simp [negative,active_matches v w hp,hb]⟩
      | some u =>
        have hm := member_support_mem w a b hab t u ha hb
        have hconst := of_decide_eq_true hc
        rw [hconst w.state] at hm
        exact ⟨positive (g.roleAtom b u),List.mem_append_right _ (List.mem_map.mpr ⟨u,hm,rfl⟩),by simp [positive,hr b u,hb]⟩
    · exact ⟨negative (g.roleAtom a t),by simp,by simp [negative,hr a t,ha]⟩
  · apply sat_map
    intro k _
    by_cases ha : w.role a = some t
    · by_cases hk : k = w.state
      · subst k
        cases hb : w.role b with
        | none => exact ⟨negative (activeAtom g b),by simp,by simp [negative,active_matches v w hp,hb]⟩
        | some u =>
          have hm := member_support_mem w a b hab t u ha hb
          exact ⟨positive (g.roleAtom b u),List.mem_append_right _ (List.mem_map.mpr ⟨u,hm,rfl⟩),by simp [positive,hr b u,hb]⟩
      · exact ⟨negative (g.stateAtom k),by simp,by simp [negative,hs k,hk]⟩
    · exact ⟨negative (g.roleAtom a t),by simp,by simp [negative,hr a t,ha]⟩

theorem embedding_sat {n : Nat} {c : Host} {g : Geometry n} (v : Valuation)
    (w : LocalWitness c g) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) : FormulaSat v (embeddingClauses g) := by
  simp only [embeddingClauses,formulaSat_append]
  refine ⟨⟨⟨⟨oneHot_sat v _ w.state hs,?_⟩,?_⟩,?_⟩,?_⟩
  · exact sat_flatMap v _ _ fun m _ => domains_sat v w hp hr m
  · apply sat_flatMap
    rintro ⟨a,b⟩ hab
    exact sat_map v _ _ fun t _ => injection_sat v w hr a b (ne_of_lt (mem_pairs.mp hab)) t
  · apply sat_flatMap; intro m _
    apply sat_flatMap; intro t _
    exact sat_flatMap v _ _ fun a _ => anchor_sat v w hp hr hs m t a
  · apply sat_flatMap
    rintro ⟨a,b⟩ hab
    exact sat_flatMap v _ _ fun t _ => member_sat v w hp hr hs a b (ne_of_lt (mem_pairs.mp hab)) t

#print axioms embedding_sat
end UniformK60.BalancedEncoding
