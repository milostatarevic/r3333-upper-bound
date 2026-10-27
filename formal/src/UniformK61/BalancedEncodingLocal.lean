import UniformK61.BalancedEncodingDefs

/-! Soundness of the shared-state local embedding clauses. -/
set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

theorem mem_pairs {n : Nat} {a b : Fin n} : (a,b) ∈ pairs n ↔ a < b := by
  simp [pairs]

theorem sat_map {α : Type} (v : Valuation) (xs : List α) (f : α → List Literal)
    (h : ∀ x ∈ xs, ClauseSat v (f x)) : FormulaSat v (xs.map f) := by
  intro clause hm
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hm
  exact h x hx

theorem sat_flatMap {α : Type} (v : Valuation) (xs : List α) (f : α → CNF)
    (h : ∀ x ∈ xs, FormulaSat v (f x)) : FormulaSat v (xs.flatMap f) := by
  intro clause hm
  obtain ⟨x,hx,hc⟩ := List.mem_flatMap.mp hm
  exact h x hx clause hc

theorem sat_of_mem (v : Valuation) (ls : List Literal) (lit : Literal)
    (hm : lit ∈ ls) (h : v lit.2 = lit.1) : ClauseSat v ls := ⟨lit,hm,h⟩

theorem oneHot_sat {n : Nat} (v : Valuation) (vars : Fin n → Nat) (chosen : Fin n)
    (h : ∀ i, v (vars i) = decide (i = chosen)) : FormulaSat v (oneHot vars) := by
  rw [oneHot,formulaSat_append]
  constructor
  · intro clause hc
    simp only [List.mem_singleton] at hc; subst clause
    exact ⟨positive (vars chosen),List.mem_map.mpr ⟨chosen,by simp,rfl⟩,by simp [positive,h]⟩
  · apply sat_map
    rintro ⟨a,b⟩ hp
    have hab := mem_pairs.mp hp
    by_cases ha : a = chosen
    · have hb : b ≠ chosen := by intro hb; subst a; subst b; exact (lt_irrefl _ hab)
      exact ⟨negative (vars b),by simp,by simp [negative,h,hb]⟩
    · exact ⟨negative (vars a),by simp,by simp [negative,h,ha]⟩

def PhysicalMatches (v : Valuation) (c : Host) : Prop :=
  ∀ u w : Vertex, u ≠ w → ∀ q, v (edgeVar u w q) = decide (c u w = palette q)

def RoleMatches {c : Host} {o : Owner} {s : Scope} (v : Valuation) (w : LocalWitness c o s) : Prop :=
  ∀ m t, v (roleAtom s m t) = decide (w.role m = some t)
def StateMatches {c : Host} {o : Owner} {s : Scope} (v : Valuation) (w : LocalWitness c o s) : Prop :=
  ∀ k, v (stateAtom s k) = decide (k = w.state)

set_option maxRecDepth 10000 in
theorem own_other_ne : ∀ s m n, ownVertex s m ≠ otherVertex s n := by decide

theorem active_matches {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hp : PhysicalMatches v c) (m : Fin 16) :
    v (activeAtom s m) = (w.role m).isSome := by
  rw [activeAtom,hp _ _ (own_other_ne s _ _),w.active]

theorem domains_sat {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hp : PhysicalMatches v c) (hr : RoleMatches v w) (m : Fin 16) :
    FormulaSat v (domains s m) := by
  simp only [domains,formulaSat_append]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro clause hc
    simp only [List.mem_singleton] at hc; subst clause
    cases hh : w.role m with
    | none => exact ⟨negative (activeAtom s m),by simp,by simp [negative,active_matches v w hp,hh]⟩
    | some t =>
      exact ⟨positive (roleAtom s m t),by simp,by simp [positive,hr m t,hh]⟩
  · apply sat_map
    intro t _
    by_cases hh : w.role m = some t
    · exact ⟨positive (activeAtom s m),by simp,by simp [positive,active_matches v w hp,hh]⟩
    · exact ⟨negative (roleAtom s m t),by simp,by simp [negative,hr m t,hh]⟩
  · apply sat_map
    rintro ⟨t,u⟩ hm
    have htu : t ≠ u := ne_of_lt (mem_pairs.mp hm)
    by_cases hh : w.role m = some t
    · have hu : w.role m ≠ some u := by simpa [hh] using htu
      exact ⟨negative (roleAtom s m u),by simp,by simp [negative,hr m u,hu]⟩
    · exact ⟨negative (roleAtom s m t),by simp,by simp [negative,hr m t,hh]⟩

theorem injection_sat {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hr : RoleMatches v w) (a b : Fin 16) (hab : a ≠ b) (t : Fin 11) :
    ClauseSat v [negative (roleAtom s a t),negative (roleAtom s b t)] := by
  by_cases hh : w.role a = some t
  · have hb : w.role b ≠ some t := fun hb => hab (w.injective a b t hh hb)
    exact ⟨negative (roleAtom s b t),by simp,by simp [negative,hr b t,hb]⟩
  · exact ⟨negative (roleAtom s a t),by simp,by simp [negative,hr a t,hh]⟩

theorem anchor_sat {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) (m : Fin 16) (t : Fin 11) (a : Fin 5) :
    FormulaSat v (anchorClauses o s m t a) := by
  have hphys (q : Color) : v (anchorAtom o s m a q) = decide (c (anchorVertex o s a) (otherVertex s m) = palette q) :=
    hp _ _ (own_other_ne s _ _) q
  unfold anchorClauses
  split_ifs with hc
  · intro clause hm
    simp only [List.mem_singleton] at hm; subst clause
    by_cases hh : w.role m = some t
    · have hconst := of_decide_eq_true hc
      have he := w.anchors m t hh a
      rw [hconst w.state] at he
      exact ⟨positive (anchorAtom o s m a (statePhysicalColor s 0 a t)),by simp,by simp [positive,hphys,he]⟩
    · exact ⟨negative (roleAtom s m t),by simp,by simp [negative,hr m t,hh]⟩
  · rw [formulaSat_append]
    constructor
    · apply sat_map
      intro q hq
      have hnot : ¬ ∃ k : Fin 6, statePhysicalColor s k a t = foreign (scopeColor s) q := by
        simpa [possibleAnchor] using (List.mem_filter.mp hq).2
      by_cases hh : w.role m = some t
      · have he := w.anchors m t hh a
        have hne : c (anchorVertex o s a) (otherVertex s m) ≠ palette (foreign (scopeColor s) q) := by
          rw [he]
          intro hh
          exact hnot ⟨w.state,palette_injective hh⟩
        exact ⟨negative (anchorAtom o s m a (foreign (scopeColor s) q)),by simp,by simp [negative,hphys,hne]⟩
      · exact ⟨negative (roleAtom s m t),by simp,by simp [negative,hr m t,hh]⟩
    · apply sat_map
      intro k _
      by_cases hh : w.role m = some t
      · by_cases hk : k = w.state
        · subst k
          exact ⟨positive (anchorAtom o s m a (statePhysicalColor s w.state a t)),by simp,
            by simp [positive,hphys,w.anchors m t hh a]⟩
        · exact ⟨negative (stateAtom s k),by simp,by simp [negative,hs k,hk]⟩
      · exact ⟨negative (roleAtom s m t),by simp,by simp [negative,hr m t,hh]⟩

theorem member_support_mem {c : Host} {o : Owner} {s : Scope} (w : LocalWitness c o s)
    (a b : Fin 16) (hab : a ≠ b) (t u : Fin 11) (ha : w.role a = some t) (hb : w.role b = some u) :
    u ∈ memberSupport w.state (memberColor o s a b) t := by
  have hut : u ≠ t := by
    intro h; subst u; exact hab (w.injective a b t ha hb)
  simp [memberSupport,hut,w.members a b t u hab ha hb]

theorem member_sat {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) (a b : Fin 16) (hab : a ≠ b) (t : Fin 11) :
    FormulaSat v (memberClauses o s a b t) := by
  simp only [memberClauses]
  split_ifs with hc
  · intro clause hm
    simp only [List.mem_singleton] at hm; subst clause
    by_cases ha : w.role a = some t
    · cases hb : w.role b with
      | none => exact ⟨negative (activeAtom s b),by simp,by simp [negative,active_matches v w hp,hb]⟩
      | some u =>
        have hm := member_support_mem w a b hab t u ha hb
        have hconst := of_decide_eq_true hc
        rw [hconst w.state] at hm
        exact ⟨positive (roleAtom s b u),List.mem_append_right _ (List.mem_map.mpr ⟨u,hm,rfl⟩),by simp [positive,hr b u,hb]⟩
    · exact ⟨negative (roleAtom s a t),by simp,by simp [negative,hr a t,ha]⟩
  · apply sat_map
    intro k _
    by_cases ha : w.role a = some t
    · by_cases hk : k = w.state
      · subst k
        cases hb : w.role b with
        | none => exact ⟨negative (activeAtom s b),by simp,by simp [negative,active_matches v w hp,hb]⟩
        | some u =>
          have hm := member_support_mem w a b hab t u ha hb
          exact ⟨positive (roleAtom s b u),List.mem_append_right _ (List.mem_map.mpr ⟨u,hm,rfl⟩),by simp [positive,hr b u,hb]⟩
      · exact ⟨negative (stateAtom s k),by simp,by simp [negative,hs k,hk]⟩
    · exact ⟨negative (roleAtom s a t),by simp,by simp [negative,hr a t,ha]⟩

theorem embedding_sat {c : Host} {o : Owner} {s : Scope} (v : Valuation)
    (w : LocalWitness c o s) (hp : PhysicalMatches v c)
    (hr : RoleMatches v w) (hs : StateMatches v w) : FormulaSat v (embeddingClauses o s) := by
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
end UniformK61.BalancedEncoding
