import PricingC.BoundaryAnchor
import PricingIntegration.SeedCensusInvariants

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open PricingIntegration.SeedCensus PricingIntegration.SeedBinding

 def AlignedPair.changeBoundary {c : Host} {b : Boundary} (p : AlignedPair c b)
    (b' : Boundary) (hp : pair b' = pair b) (ho : omitted b' = omitted b) : AlignedPair c b' where
  physical := p.physical
  pair_match := hp.trans p.pair_match
  present_match := by intro a; rw [p.present_match a,ho]

 def FullReferenceScope.restate {c : Host} {owner : Vertex} {omitted : FourColor}
    {pal : Fin 3 ≃ {q : FourColor // q ≠ omitted}} {state : Fin 72}
    (y : FullReferenceScope c owner omitted pal state) (state' : Fin 72) (h : state = state') :
    FullReferenceScope c owner omitted pal state' where
  present := y.present
  vertex := y.vertex
  mem_scope := y.mem_scope
  covers := y.covers
  map_color := by intro i j hij; rw [←h]; exact y.map_color i j hij
  full := y.full

structure AlignedTriple (c : Host) (b : Boundary) where
  xs : AlignedPair c b
  y : FullReferenceScope c 0 (palette 1) paletteY (yState b)
  agreement : ∀ (j : Fin 5) (hj : j.val < size b),
    y.at (yRole b j) = xs.physical.s.vertex ⟨anchorSource b j,xs.anchor_present j hj⟩

 def SameAnchor (b b' : Boundary) : Prop :=
  pair b' = pair b ∧ omitted b' = omitted b ∧ size b' = size b ∧
  ∀ j : Fin 5, j.val < size b → anchorSource b' j = anchorSource b j

 theorem sameAnchor_eraseY (b : Boundary) : SameAnchor (eraseY b) b := by
  have h := eraseY_fields b
  exact ⟨h.1.symm,h.2.1.symm,h.2.2.1.symm,fun j _ => anchorSource_eraseY b j⟩

/-- Completing Y's matrix changes none of the already fixed physical S/X
identifications. Only its retained reference row is selected. -/
theorem complete_five_aligned (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (b : Boundary) (p : AlignedPair c b) (hsize : size b = 5)
    (make : Fin 6 → Boundary)
    (hsame : ∀ i, SameAnchor b (make i))
    (hstate : ∀ i, yState (make i) = AnchorTables.anchoredIndex i)
    (hroles : ∀ i, yRole (make i) = generators) :
    ∃ i : Fin 6, Nonempty (AlignedTriple c (make i)) := by
  let a := p.anchor 5 hsize.symm (by decide)
  have hcyc : ∀ j k, j ≠ k → c (a j) (a k) = (paletteY (AnchorTables.cycleColor j k)).val := by
    intro j k hjk
    exact (p.anchor_color 5 hsize.symm (by decide) j k hjk).trans (canonical_cycle_binding b hsize j k hjk)
  obtain ⟨i,y,hy⟩ := physical_Y_five c hc hroot a
    (p.anchor_in_Y 5 hsize.symm (by decide)) (p.anchor_in_S 5 hsize.symm (by decide)) hcyc
  let p' := p.changeBoundary (make i) (hsame i).1 (hsame i).2.1
  let y' := y.restate (yState (make i)) (hstate i).symm
  refine ⟨i,⟨⟨p',y',?_⟩⟩⟩
  intro j hj
  have hj0 : j.val < size b := by rw [←(hsame i).2.2.1]; exact hj
  have he := (hsame i).2.2.2 j hj0
  change y.at (yRole (make i) j) = _
  rw [hroles i,hy j]
  apply congrArg p.physical.s.vertex
  exact Subtype.ext he.symm

 theorem complete_four_aligned (c : Host) (hc : NoMonochromaticTriangle c)
    (hroot : RootConditions c) (b : Boundary) (p : AlignedPair c b) (hsize : size b = 4)
    (star : Fin 6 → Boundary) (plane : Fin 2 → Boundary)
    (hsame : ∀ i, SameAnchor b (star i)) (hpsame : ∀ i, SameAnchor b (plane i))
    (hstate : ∀ i, yState (star i) = AnchorTables.anchoredIndex i)
    (hpstate : ∀ i, yState (plane i) = FourAnchorTables.nonstarIndex i)
    (hroles : ∀ i (j : Fin 4), yRole (star i) j.castSucc = FourAnchorTables.starRoles j)
    (hproles : ∀ i (j : Fin 4), yRole (plane i) j.castSucc = FourAnchorTables.planeRoles j) :
    (∃ i : Fin 6, Nonempty (AlignedTriple c (star i))) ∨
    (∃ i : Fin 2, Nonempty (AlignedTriple c (plane i))) := by
  let a := p.anchor 4 hsize.symm (by decide)
  have hp : ∀ j k, j ≠ k → c (a j) (a k) = (paletteY (FourAnchorTables.pathColor j k)).val := by
    intro j k hjk
    exact (p.anchor_color 4 hsize.symm (by decide) j k hjk).trans (canonical_path_binding b hsize j k hjk)
  rcases physical_Y_four c hc hroot a
    (p.anchor_in_Y 4 hsize.symm (by decide)) (p.anchor_in_S 4 hsize.symm (by decide)) hp with
    ⟨i,y,hy⟩ | ⟨i,y,hy⟩
  · let p' := p.changeBoundary (star i) (hsame i).1 (hsame i).2.1
    let y' := y.restate (yState (star i)) (hstate i).symm
    refine Or.inl ⟨i,⟨⟨p',y',?_⟩⟩⟩
    intro j hj
    have hj0 : j.val < 4 := by simpa only [(hsame i).2.2.1,hsize] using hj
    let k : Fin 4 := ⟨j.val,hj0⟩
    have hkj : k.castSucc = j := Fin.ext rfl
    have he := (hsame i).2.2.2 j (by omega)
    change y.at (yRole (star i) j) = _
    have hrole : yRole (star i) j = FourAnchorTables.starRoles k := by rw [←hkj]; exact hroles i k
    rw [hrole,hy k]
    apply congrArg p.physical.s.vertex
    apply Subtype.ext
    change anchorSource b k.castSucc = _
    rw [hkj]
    exact he.symm
  · let p' := p.changeBoundary (plane i) (hpsame i).1 (hpsame i).2.1
    let y' := y.restate (yState (plane i)) (hpstate i).symm
    refine Or.inr ⟨i,⟨⟨p',y',?_⟩⟩⟩
    intro j hj
    have hj0 : j.val < 4 := by simpa only [(hpsame i).2.2.1,hsize] using hj
    let k : Fin 4 := ⟨j.val,hj0⟩
    have hkj : k.castSucc = j := Fin.ext rfl
    have he := (hpsame i).2.2.2 j (by omega)
    change y.at (yRole (plane i) j) = _
    have hrole : yRole (plane i) j = FourAnchorTables.planeRoles k := by rw [←hkj]; exact hproles i k
    rw [hrole,hy k]
    apply congrArg p.physical.s.vertex
    apply Subtype.ext
    change anchorSource b k.castSucc = _
    rw [hkj]
    exact he.symm

#print axioms complete_five_aligned
#print axioms complete_four_aligned
end PricingC
