import UniformK60.HostNormalizationPartial

/-! Extend all prescribed actual vertices together, inside their root cells.
This is shared by complete marked templates and by punctured references. -/
set_option autoImplicit false
namespace UniformK60.CommonPlacement
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization

/-- One whole-host equivalence simultaneously realizes all prescribed
critical and support coordinates while keeping every root spoke correct. -/
theorem exists_root_placement {A : Type*} [Finite A]
    (c : Host) (r : Vertex) (cell : Vertex → Option FourColor)
    (hzero : ∀ v,cell v=none ↔ v=0)
    (hd : ∀ q : FourColor,Fintype.card {v // cell v=some q}=colorDegree c q r)
    (source target : A ↪ Vertex)
    (hlabel : ∀ a,rootCell c r (Equiv.refl _) (target a)=cell (source a)) :
    ∃ e : Vertex ≃ Vertex,e 0=r ∧
      (∀ v,rootCell c r (Equiv.refl _) (e v)=cell v) ∧
      ∀ a,e (source a)=target a := by
  obtain ⟨e,he0,he⟩ := exists_root_cell_equiv c r (Equiv.refl _) cell hzero hd
  let source' : A ↪ Vertex := source.trans e.toEmbedding
  have hp : ∀ a,rootCell c r (Equiv.refl _) (target a)=
      rootCell c r (Equiv.refl _) (source' a) := by
    intro a
    exact (hlabel a).trans (he (source a)).symm
  obtain ⟨p,hp,hl⟩ := extend_partial_label_preserving
    (rootCell c r (Equiv.refl _)) source' target hp
  have hlabels (v : Vertex) : rootCell c r (Equiv.refl _) ((e.trans p) v)=cell v :=
    (hl (e v)).trans (he v)
  refine ⟨e.trans p,?_,hlabels,hp⟩
  exact (rootCell_none c r ((e.trans p) 0) (Equiv.refl _)).mp
    ((hlabels 0).trans ((hzero 0).mpr rfl))

/-- Root plus four disjoint sets of actual root-neighborhood vertices. -/
abbrev Parts (sizes : Color → Nat) := Unit ⊕ (q : Color) × Fin (sizes q)

def partsMap {c : Host} {r : Vertex} {sizes : Color → Nat}
    (maps : ∀ q,Fin (sizes q) ↪ Vertex) : Parts sizes → Vertex
  | .inl _ => r
  | .inr ⟨q,i⟩ => maps q i

theorem partsMap_injective {c : Host} {r : Vertex} {sizes : Color → Nat}
    (maps : ∀ q,Fin (sizes q) ↪ Vertex)
    (mem : ∀ q i,maps q i ∈ colorNeighborhood c (palette q) r) :
    Function.Injective (partsMap (c:=c) (r:=r) maps) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a;cases b;rfl
    | inr b =>
      exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (mem b.1 b.2)).1 hab.symm)
  | inr a =>
    cases b with
    | inl b =>
      exact False.elim (((mem_colorNeighborhood _ _ _ _).mp (mem a.1 a.2)).1 hab)
    | inr b =>
      rcases a with ⟨q,i⟩
      rcases b with ⟨s,j⟩
      have hq : q=s := by
        apply palette_injective
        exact (((mem_colorNeighborhood _ _ _ _).mp (mem q i)).2.symm.trans
          (congrArg (c r) hab)).trans (((mem_colorNeighborhood _ _ _ _).mp (mem s j)).2)
      subst s
      have hij : i=j := (maps q).injective hab
      subst j
      rfl

def partsEmbedding {c : Host} {r : Vertex} {sizes : Color → Nat}
    (maps : ∀ q,Fin (sizes q) ↪ Vertex)
    (mem : ∀ q i,maps q i ∈ colorNeighborhood c (palette q) r) : Parts sizes ↪ Vertex :=
  ⟨partsMap maps,partsMap_injective maps mem⟩

#print axioms exists_root_placement
#print axioms partsMap_injective
end UniformK60.CommonPlacement
