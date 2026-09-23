import PricingC.ScopeOmission
import PricingC.PhysicalTags
import PricingIntegration.SeedCensus

namespace PricingC
open Finset Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open PricingIntegration.SeedCensus PricingIntegration.SeedBinding

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
 theorem anchor_source_B : ∀ (b : Boundary) (j : Fin 5), j.val < size b →
    anchorSource b j ≠ 0 ∧ PricingG.Completion72.referenceColor (PairTables.representativeS (pair b)) 0 (anchorSource b j) = 1 := by decide +kernel

structure AlignedPair (c : Host) (b : Boundary) where
  physical : PhysicalXSPair c
  pair_match : pair b = physical.pair
  present_match : ∀ a : Fin 16, a ∈ physical.s.present ↔ omitted b ≠ some a

 theorem AlignedPair.anchor_present {c : Host} {b : Boundary} (p : AlignedPair c b)
    (j : Fin 5) (hj : j.val < size b) : anchorSource b j ∈ p.physical.s.present := by
  apply (p.present_match _).mpr
  exact (s_present_exact b _).mp (anchor_overlap b j hj).2

noncomputable def AlignedPair.anchor {c : Host} {b : Boundary} (p : AlignedPair c b)
    (n : Nat) (hn : n = size b) (h5 : n ≤ 5) : Fin n ↪ Vertex where
  toFun j := p.physical.s.vertex ⟨anchorSource b (j.castLE h5),
    p.anchor_present (j.castLE h5) (by change j.val < size b; omega)⟩
  inj' := by
    intro i j h
    have hs := congrArg Subtype.val (p.physical.s.vertex.injective h)
    have he := anchor_source_injective b (i.castLE h5) (j.castLE h5)
      (by change i.val < size b; omega) (by change j.val < size b; omega) hs
    exact Fin.ext (congrArg (fun z : Fin 5 => z.val) he)

 theorem AlignedPair.anchor_in_S {c : Host} {b : Boundary} (p : AlignedPair c b)
    (n : Nat) (hn : n = size b) (h5 : n ≤ 5) (j : Fin n) :
    p.anchor n hn h5 j ∈ colorNeighborhood c (palette 2) 33 := p.physical.s.mem_scope _

 theorem AlignedPair.anchor_in_Y {c : Host} {b : Boundary} (p : AlignedPair c b)
    (n : Nat) (hn : n = size b) (h5 : n ≤ 5) (j : Fin n) :
    p.anchor n hn h5 j ∈ colorNeighborhood c (palette 1) 0 := by
  have hj : (j.castLE h5).val < size b := by change j.val < size b; omega
  have hs := anchor_source_B b (j.castLE h5) hj
  let v : p.physical.s.present := ⟨anchorSource b (j.castLE h5),p.anchor_present _ hj⟩
  have hv : v.val ≠ 0 := hs.1
  have hne : (⟨0,p.physical.root_present⟩ : p.physical.s.present) ≠ v :=
    fun h => hv (congrArg Subtype.val h).symm
  have hc := p.physical.s.map_color ⟨0,p.physical.root_present⟩ v hne
  rw [p.physical.root_image] at hc
  have hsource : PricingG.Completion72.referenceColor (PairTables.representativeS p.physical.pair) 0 (anchorSource b (j.castLE h5)) = 1 := by
    rw [←p.pair_match]
    exact hs.2
  change c 0 (p.physical.s.vertex v) = (paletteS (PricingG.Completion72.referenceColor (PairTables.representativeS p.physical.pair) 0 (anchorSource b (j.castLE h5)))).val at hc
  rw [hsource] at hc
  apply (mem_colorNeighborhood c _ _ _).mpr
  refine ⟨?_,hc⟩
  intro he
  have he' := p.physical.s.vertex.injective (he.trans p.physical.root_image.symm)
  exact hv (congrArg Subtype.val he')

 theorem AlignedPair.anchor_color {c : Host} {b : Boundary} (p : AlignedPair c b)
    (n : Nat) (hn : n = size b) (h5 : n ≤ 5) (j k : Fin n) (hjk : j ≠ k) :
    c (p.anchor n hn h5 j) (p.anchor n hn h5 k) =
      palette (canonicalColor b (j.castLE h5) (k.castLE h5)) := by
  have hj : (j.castLE h5).val < size b := by change j.val < size b; omega
  have hk : (k.castLE h5).val < size b := by change k.val < size b; omega
  have hne : j.castLE h5 ≠ k.castLE h5 := fun h => hjk (Fin.ext (congrArg (fun z : Fin 5 => z.val) h))
  have hsrc : anchorSource b (j.castLE h5) ≠ anchorSource b (k.castLE h5) :=
    fun h => hne (anchor_source_injective b _ _ hj hk h)
  have hm := p.physical.s.map_color
    ⟨anchorSource b (j.castLE h5),p.anchor_present _ hj⟩
    ⟨anchorSource b (k.castLE h5),p.anchor_present _ hk⟩
    (fun h => hsrc (congrArg Subtype.val h))
  have hsource : scopePalette 1 (PricingG.Completion72.referenceColor (PairTables.representativeS p.physical.pair)
      (anchorSource b (j.castLE h5)) (anchorSource b (k.castLE h5))) = canonicalColor b (j.castLE h5) (k.castLE h5) := by
    rw [←p.pair_match]
    exact anchor_source_colors b _ _ hj hk hne
  exact hm.trans ((paletteS_binding _).trans (congrArg palette hsource))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
 theorem canonical_cycle_binding : ∀ (b : Boundary), size b = 5 → ∀ j k : Fin 5,
    j ≠ k → palette (canonicalColor b j k) = (paletteY (AnchorTables.cycleColor j k)).val := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
 theorem canonical_path_binding : ∀ (b : Boundary), size b = 4 → ∀ j k : Fin 4,
    j ≠ k → palette (canonicalColor b j.castSucc k.castSucc) = (paletteY (FourAnchorTables.pathColor j k)).val := by decide +kernel

#print axioms AlignedPair.anchor_color
end PricingC
