import PricingIntegration.SeedOverlap
import PricingIntegration.SaturatedGluing

namespace PricingIntegration.SeedBinding
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open PricingIntegration.SeedCensus

abbrev Present (m : Metadata) (s : Fin 3) := {a : Fin 16 // (m.maps s a).isSome = true}

def canonical (m : Metadata) (s : Fin 3) (a : Present m s) : Vertex :=
  (m.maps s a.val).getD 0

theorem canonical_some (m : Metadata) (s : Fin 3) (a : Present m s) :
    m.maps s a.val = some (canonical m s a) := by
  cases h : m.maps s a.val with
  | none => have ha := a.property; simp [h] at ha
  | some v => simp [canonical,h]

theorem canonical_injective (b : Boundary) (s : Fin 3) :
    Function.Injective (canonical (metadata (index b)) s) := by
  intro a d h
  apply Subtype.ext
  apply scope_maps_injective b s a.val d.val a.property
  rw [canonical_some _ _ a,canonical_some _ _ d,h]

def scopeDomain (m : Metadata) (s : Fin 3) : Finset Vertex :=
  Finset.univ.filter fun v => ∃ a : Fin 16, m.maps s a = some v

theorem mem_scopeDomain (m : Metadata) (s : Fin 3) (v : Vertex) :
    v ∈ scopeDomain m s ↔ ∃ a : Present m s, canonical m s a = v := by
  constructor
  · intro hv
    obtain ⟨a,ha⟩ := (Finset.mem_filter.mp hv).2
    refine ⟨⟨a,by simp [ha]⟩,?_⟩
    simp [canonical,ha]
  · rintro ⟨a,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val,canonical_some m s a⟩

noncomputable def transport (m : Metadata) (s : Fin 3)
    (actual : Present m s ↪ Vertex) (v : Vertex) : Vertex :=
  if h : ∃ a : Present m s, canonical m s a = v then actual (Classical.choose h) else 0

theorem transport_at (b : Boundary) (s : Fin 3)
    (actual : Present (metadata (index b)) s ↪ Vertex)
    (a : Present (metadata (index b)) s) :
    transport (metadata (index b)) s actual (canonical _ _ a) = actual a := by
  have h : ∃ d : Present (metadata (index b)) s, canonical _ _ d = canonical _ _ a := ⟨a,rfl⟩
  rw [transport,dif_pos h]
  exact congrArg actual (canonical_injective b s (Classical.choose_spec h))

theorem transport_injective (b : Boundary) (s : Fin 3)
    (actual : Present (metadata (index b)) s ↪ Vertex) :
    Set.InjOn (transport (metadata (index b)) s actual) (scopeDomain (metadata (index b)) s) := by
  intro u hu v hv h
  obtain ⟨a,rfl⟩ := (mem_scopeDomain _ _ _).mp hu
  obtain ⟨d,rfl⟩ := (mem_scopeDomain _ _ _).mp hv
  rw [transport_at b s actual a,transport_at b s actual d] at h
  exact congrArg (canonical _ _) (actual.injective h)

theorem transport_tags (b : Boundary) (s : Fin 3)
    (actual : Present (metadata (index b)) s ↪ Vertex)
    (htags : ∀ a, physicalTag (actual a) = physicalTag (canonical _ _ a)) :
    ∀ v ∈ scopeDomain (metadata (index b)) s,
      physicalTag (transport (metadata (index b)) s actual v) = physicalTag v := by
  intro v hv
  obtain ⟨a,rfl⟩ := (mem_scopeDomain _ _ _).mp hv
  rw [transport_at b s actual a]
  exact htags a

theorem transported_agreement (b : Boundary) (s t : Fin 3)
    (a : Present (metadata (index b)) s ↪ Vertex)
    (d : Present (metadata (index b)) t ↪ Vertex)
    (hagree : ∀ x y, canonical _ _ x = canonical _ _ y → a x = d y) :
    ∀ v ∈ scopeDomain (metadata (index b)) s, v ∈ scopeDomain (metadata (index b)) t →
      transport (metadata (index b)) s a v = transport (metadata (index b)) t d v := by
  intro v hs ht
  obtain ⟨x,hx⟩ := (mem_scopeDomain _ _ _).mp hs
  obtain ⟨y,hy⟩ := (mem_scopeDomain _ _ _).mp ht
  rw [←hx,transport_at b s a x]
  rw [hx,←hy,transport_at b t d y]
  exact hagree x y (hx.trans hy.symm)

#print axioms transport_injective
end PricingIntegration.SeedBinding
