import UniformK61.BalancedHost

set_option autoImplicit false
namespace UniformK61.BalancedHost
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open Ramsey61.ClassificationAdapter PricingIntegration.BActualFrame
open PricingIntegration.FixedPhysicalNeighborhood

abbrev Parts := Fin 1 ⊕ (Fin 16 ⊕ (Fin 16 ⊕ (Fin 14 ⊕ Fin 14)))

def canonical : Parts → Vertex
  | .inl _ => 0
  | .inr (.inl i) => xVertex i
  | .inr (.inr (.inl i)) => yVertex i
  | .inr (.inr (.inr (.inl i))) => pVertex i
  | .inr (.inr (.inr (.inr i))) => qVertex i

set_option maxRecDepth 20000 in
theorem canonical_bijective : Function.Bijective canonical := by decide

noncomputable def partsEquiv : Parts ≃ Vertex := Equiv.ofBijective canonical canonical_bijective

def tag : Parts → Option FourColor
  | .inl _ => none
  | .inr (.inl _) => some (palette 0)
  | .inr (.inr (.inl _)) => some (palette 1)
  | .inr (.inr (.inr (.inl _))) => some (palette 2)
  | .inr (.inr (.inr (.inr _))) => some (palette 3)

set_option maxRecDepth 20000 in
theorem canonical_tag : ∀ a : Parts, canonicalCell (canonical a) = tag a := by decide

theorem nonroot_vertex (v : Vertex) (hv : v ≠ 0) :
    ∃ u : Fin 60, BalancedHost.vertex u = v := by
  have hpos : 0 < v.val := by
    by_contra hn
    apply hv
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  refine ⟨⟨v.val-1,by have := v.isLt; omega⟩,?_⟩
  apply Fin.ext
  simp only [BalancedHost.vertex,Fin.val_mk]
  omega

theorem spokes_rootCell (c : Host) (h : Spokes c) (v : Vertex) :
    rootCell c 0 (Equiv.refl _) v = canonicalCell v := by
  by_cases hv : v = 0
  · subst v; rfl
  · obtain ⟨u,rfl⟩ := nonroot_vertex v hv
    rw [canonical_spoke]
    simp [rootCell,BalancedHost.vertex_ne_zero,h u]

def physical {c : Host} {tx ty : Bool}
    (mx : PhysicalNeighborhoodMap c 0 (palette 0) (R4333.k16Template tx))
    (my : PhysicalNeighborhoodMap c 0 (palette 1) (R4333.k16Template ty)) : Parts → Vertex
  | .inl _ => 0
  | .inr (.inl i) => mx.vertex i
  | .inr (.inr (.inl i)) => my.vertex i
  | .inr (.inr (.inr (.inl i))) => pVertex i
  | .inr (.inr (.inr (.inr i))) => qVertex i

theorem physical_tag {c : Host} (hs : Spokes c) {tx ty : Bool}
    (mx : PhysicalNeighborhoodMap c 0 (palette 0) (R4333.k16Template tx))
    (my : PhysicalNeighborhoodMap c 0 (palette 1) (R4333.k16Template ty)) (a : Parts) :
    rootCell c 0 (Equiv.refl _) (physical mx my a) = tag a := by
  rcases a with a|a|a|a|a
  · rfl
  · exact (rootCell_some c 0 _ (Equiv.refl _) _).mpr (mx.mem_neighborhood a)
  · exact (rootCell_some c 0 _ (Equiv.refl _) _).mpr (my.mem_neighborhood a)
  · rw [spokes_rootCell c hs]
    exact canonical_tag (.inr (.inr (.inr (.inl a))))
  · rw [spokes_rootCell c hs]
    exact canonical_tag (.inr (.inr (.inr (.inr a))))

private theorem same_part (a b : Parts) (h : tag a = tag b) :
    (∃ i j, a=.inl i ∧ b=.inl j) ∨
    (∃ i j, a=.inr (.inl i) ∧ b=.inr (.inl j)) ∨
    (∃ i j, a=.inr (.inr (.inl i)) ∧ b=.inr (.inr (.inl j))) ∨
    (∃ i j, a=.inr (.inr (.inr (.inl i))) ∧ b=.inr (.inr (.inr (.inl j)))) ∨
    (∃ i j, a=.inr (.inr (.inr (.inr i))) ∧ b=.inr (.inr (.inr (.inr j)))) := by
  rcases a with a|a|a|a|a <;> rcases b with b|b|b|b|b <;> simp_all [tag,palette]

theorem physical_injective {c : Host} (hs : Spokes c) {tx ty : Bool}
    (mx : PhysicalNeighborhoodMap c 0 (palette 0) (R4333.k16Template tx))
    (my : PhysicalNeighborhoodMap c 0 (palette 1) (R4333.k16Template ty)) :
    Function.Injective (physical mx my) := by
  intro a b hab
  have ht : tag a = tag b := (physical_tag hs mx my a).symm.trans
    ((congrArg (rootCell c 0 (Equiv.refl _)) hab).trans (physical_tag hs mx my b))
  rcases same_part a b ht with ⟨i,j,rfl,rfl⟩|⟨i,j,rfl,rfl⟩|⟨i,j,rfl,rfl⟩|⟨i,j,rfl,rfl⟩|⟨i,j,rfl,rfl⟩
  · exact congrArg Sum.inl (Subsingleton.elim i j)
  · exact congrArg (fun z => Sum.inr (Sum.inl z)) (mx.vertex.injective hab)
  · exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inl z))) (my.vertex.injective hab)
  · have hv := congrArg Fin.val hab
    have he : i = j := by apply Fin.ext; change i.val+33 = j.val+33 at hv; omega
    exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr (Sum.inl z)))) he
  · have hv := congrArg Fin.val hab
    have he : i = j := by apply Fin.ext; change i.val+47 = j.val+47 at hv; omega
    exact congrArg (fun z => Sum.inr (Sum.inr (Sum.inr (Sum.inr z)))) he

noncomputable def templateEquiv {c : Host} (hs : Spokes c) {tx ty : Bool}
    (mx : PhysicalNeighborhoodMap c 0 (palette 0) (R4333.k16Template tx))
    (my : PhysicalNeighborhoodMap c 0 (palette 1) (R4333.k16Template ty)) : Vertex ≃ Vertex :=
  partsEquiv.symm.trans (Equiv.ofBijective (physical mx my)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨physical_injective hs mx my,Fintype.card_congr partsEquiv⟩))

theorem templateEquiv_apply {c : Host} (hs : Spokes c) {tx ty : Bool}
    (mx : PhysicalNeighborhoodMap c 0 (palette 0) (R4333.k16Template tx))
    (my : PhysicalNeighborhoodMap c 0 (palette 1) (R4333.k16Template ty)) (a : Parts) :
    templateEquiv hs mx my (canonical a) = physical mx my a := by
  change physical mx my (partsEquiv.symm (partsEquiv a)) = _
  rw [Equiv.symm_apply_apply]

theorem named_spokes_to_templates (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : Named c) (hs : Spokes c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧ ∃ tx ty, Normalized d tx ty := by
  obtain ⟨tx,mx,hx⟩ := physical_k16_fixed_palette c hc 0 (palette 0) (hn 0 0) (foreignEquiv 0)
  obtain ⟨ty,my,hy⟩ := physical_k16_fixed_palette c hc 0 (palette 1) (hn 0 1) (foreignEquiv 1)
  let e := templateEquiv hs mx my
  let d := relabel c e (Equiv.refl _)
  have he0 : e 0 = 0 := templateEquiv_apply hs mx my (.inl 0)
  have hex (i : Fin 16) : e (xVertex i) = mx.vertex i :=
    templateEquiv_apply hs mx my (.inr (.inl i))
  have hey (i : Fin 16) : e (yVertex i) = my.vertex i :=
    templateEquiv_apply hs mx my (.inr (.inr (.inl i)))
  have helabel (v : Vertex) : rootCell c 0 (Equiv.refl _) (e v) = canonicalCell v := by
    obtain ⟨a,ha⟩ := partsEquiv.surjective v
    change canonical a = v at ha
    subst v
    rw [templateEquiv_apply]
    exact (physical_tag hs mx my a).trans (canonical_tag a).symm
  refine ⟨d,relabel_noMono c hc e (Equiv.refl _),tx,ty,⟨?_,?_,?_,?_⟩⟩
  · intro v q
    exact (relabel_degree c e (Equiv.refl _) (palette q) v).trans (hn (e v) q)
  · intro v
    have hm : e (BalancedHost.vertex v) ∈
        colorNeighborhood c (palette (BalancedHost.rootColor v)) 0 := by
      apply (rootCell_some c 0 _ (Equiv.refl _) _).mp
      rw [helabel,canonical_spoke]
      rfl
    change c (e 0) (e (BalancedHost.vertex v)) = _
    rw [he0]
    exact (mem_colorNeighborhood _ _ _ _).mp hm |>.2
  · intro i j hij
    change c (e (xVertex i)) (e (xVertex j)) = _
    rw [hex,hex,mx.map_color i j hij,hx]
    rfl
  · intro i j hij
    change c (e (yVertex i)) (e (yVertex j)) = _
    rw [hey,hey,my.map_color i j hij,hy]
    rfl

theorem uniform_to_four_owners (c : Host) (hc : NoMonochromaticTriangle c)
    (hu : UniformCommonHighPair c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧ ∃ tx ty, Normalized d tx ty := by
  obtain ⟨d,hd,hn,hs⟩ := uniform_to_named_spokes c hc hu
  exact named_spokes_to_templates d hd hn hs

#print axioms uniform_to_four_owners
end UniformK61.BalancedHost
