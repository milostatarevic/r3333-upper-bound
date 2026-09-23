import PricingC.NativeBlockActions
import Ramsey61.CEncodingCore

set_option autoImplicit false
namespace PricingG.NativeNegativeSupportTransport
open PricingC.NativeBlockAutomorphisms PricingC.NativeBlockActions

/-- The entire canonical support in each of the98 literal native role records. -/
noncomputable def canonicalSupport (r : Fin 98) : Finset (Fin (order (kind r))) :=
  ((Finset.univ : Finset (Fin 5)).filter (fun i => i.val < size r)).image
    (fun i => orderVertex r i.val)

@[simp] theorem mem_canonicalSupport (r : Fin 98) (v : Fin (order (kind r))) :
    v ∈ canonicalSupport r ↔ ∃i : Fin 5,i.val < size r ∧ orderVertex r i.val = v := by
  simp [canonicalSupport]

/-- The recorded whole-block automorphism maps the complete canonical support
onto itself. This uses the checked98 native order/role extension equations. -/
theorem canonicalSupport_map (r : Fin 98) :
    (canonicalSupport r).map (auto (kind r) (autoIndex r)).toEmbedding = canonicalSupport r := by
  apply Finset.eq_of_subset_of_card_le
  · intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨i,hi,rfl⟩ := (mem_canonicalSupport r u).mp hu
    have hb := (all_role_bounds r i hi).2
    have hb5 : inducedLabel r i.val < 5 := by
      rcases size_four_or_five r with h | h <;> omega
    apply (mem_canonicalSupport r _).mpr
    refine ⟨⟨inducedLabel r i.val,hb5⟩,hb,?_⟩
    exact (all_role_extensions r i hi).symm
  · simp

/-- Positive membership is invariant for every vertex of the complete15/16
block, including vertices outside the four/five support. -/
theorem auto_mem_iff (r : Fin 98) (v : Fin (order (kind r))) :
    auto (kind r) (autoIndex r) v ∈ canonicalSupport r ↔ v ∈ canonicalSupport r := by
  nth_rw 1 [←canonicalSupport_map r]
  simp only [Finset.mem_map,Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨a,ha,he⟩
    have hav : a=v := (auto (kind r) (autoIndex r)).injective he
    simpa only [hav] using ha
  · intro hv
    exact ⟨v,hv,rfl⟩

/-- Negative support membership is preserved as well as positive membership. -/
theorem auto_not_mem_iff (r : Fin 98) (v : Fin (order (kind r))) :
    auto (kind r) (autoIndex r) v ∉ canonicalSupport r ↔ v ∉ canonicalSupport r :=
  not_congr (auto_mem_iff r v)

/-- A complete physical support biconditional transports through the actual
native whole-block reindexing, with the same host, mark and physical color. -/
theorem physical_marked_support_iff {V C : Type} (r : Fin 98)
    (physical : Fin (order (kind r)) ↪ V) (host : V → V → C)
    (mark : V) (q : C)
    (h : ∀v,host mark (physical v)=q ↔ v ∈ canonicalSupport r)
    (v : Fin (order (kind r))) :
    host mark (reindex (kind r) (autoIndex r) physical v)=q ↔ v ∈ canonicalSupport r := by
  change host mark (physical (auto (kind r) (autoIndex r) v))=q ↔ _
  exact (h _).trans (auto_mem_iff r v)

/-- This is the negative unit needed by the native signed-support suffix. -/
theorem physical_marked_non_support_iff {V C : Type} (r : Fin 98)
    (physical : Fin (order (kind r)) ↪ V) (host : V → V → C)
    (mark : V) (q : C)
    (h : ∀v,host mark (physical v)=q ↔ v ∈ canonicalSupport r)
    (v : Fin (order (kind r))) :
    host mark (reindex (kind r) (autoIndex r) physical v)≠q ↔ v ∉ canonicalSupport r :=
  not_congr (physical_marked_support_iff r physical host mark q h v)

/-- Both polarities of the actual edge-to-mark fact are preserved on every
whole-block label; no statement is restricted to the listed support rows. -/
theorem physical_marked_polarities {V C : Type} (r : Fin 98)
    (physical : Fin (order (kind r)) ↪ V) (host : V → V → C)
    (mark : V) (q : C)
    (h : ∀v,host mark (physical v)=q ↔ v ∈ canonicalSupport r)
    (v : Fin (order (kind r))) :
    (host mark (reindex (kind r) (autoIndex r) physical v)=q ↔ host mark (physical v)=q) ∧
    (host mark (reindex (kind r) (autoIndex r) physical v)≠q ↔ host mark (physical v)≠q) := by
  have hp := (physical_marked_support_iff r physical host mark q h v).trans (h v).symm
  exact ⟨hp,not_congr hp⟩

/-- Actual-host form: an exact whole-block neighborhood/support biconditional
supplies both positive and negative edge units after the native action. -/
theorem actual_host_signed_support (c : Ramsey61.Host) (r : Fin 98)
    (physical : Fin (order (kind r)) ↪ Ramsey61.CEncodingCore.Vertex)
    (mark : Ramsey61.CEncodingCore.Vertex) (q : Ramsey61.FourColor)
    (hmark : ∀v,physical v≠mark)
    (hsupport : ∀v,physical v∈Ramsey61.colorNeighborhood c q mark ↔ v∈canonicalSupport r)
    (v : Fin (order (kind r))) :
    (c mark (reindex (kind r) (autoIndex r) physical v)=q ↔ c mark (physical v)=q) ∧
    (c mark (reindex (kind r) (autoIndex r) physical v)≠q ↔ c mark (physical v)≠q) := by
  have h : ∀u,c mark (physical u)=q ↔ u∈canonicalSupport r := by
    intro u
    constructor
    · intro he
      exact (hsupport u).mp ((Ramsey61.mem_colorNeighborhood _ _ _ _).mpr ⟨hmark u,he⟩)
    · intro hu
      exact ((Ramsey61.mem_colorNeighborhood _ _ _ _).mp ((hsupport u).mpr hu)).2
  exact physical_marked_polarities r physical (fun x y=>c x y) mark q h v

#print axioms actual_host_signed_support

#print axioms canonicalSupport_map
#print axioms auto_not_mem_iff
#print axioms physical_marked_polarities
end PricingG.NativeNegativeSupportTransport
