import PricingABD.TTExchange
import PricingABD.FiniteSupportsFast

namespace PricingABD.SupportTransport
open Ramsey61 Ramsey61.CEncodingCore PricingABD.TTExchange
open PricingABD.FiniteSupportsFast
open Finset

/-- Vertices in differently colored actual root cells are distinct. -/
theorem distinct_root_cells {c : Host} {r u v : Fin 61} {q p : FourColor}
    (hu : u ∈ colorNeighborhood c q r) (hv : v ∈ colorNeighborhood c p r) (hqp : q ≠ p) : u ≠ v := by
  intro heq
  have h1 := ((mem_colorNeighborhood c q r u).mp hu).2
  have h2 := ((mem_colorNeighborhood c p r v).mp hv).2
  subst v
  exact hqp (h1.symm.trans h2)

theorem actual_left_support_avoids {c : Host} {k : Nat} {t : Bool}
    (f : Frame c k t) (hc : NoMonochromaticTriangle c) : ProperFive (leftSupport f) := by
  intro a ha b hb hab hcolor
  have hma : f.marked 15 ≠ f.left a := distinct_root_cells (f.marked_mem 15) (f.left_mem a) (by decide)
  have hmb : f.marked 15 ≠ f.left b := distinct_root_cells (f.marked_mem 15) (f.left_mem b) (by decide)
  have hma3 := (mem_filter.mp ha).2
  have hmb3 := (mem_filter.mp hb).2
  have he := f.left_edges a b hab
  change R4333.k15Twisted a b = 2 at hcolor
  rw [hcolor] at he
  exact hc (f.marked 15) (f.left a) (f.left b) ⟨hma,hmb,f.left.injective.ne hab⟩
    ⟨hma3.trans hmb3.symm,hmb3.trans he.symm⟩

theorem actual_right_support_avoids {c : Host} {k : Nat} {t : Bool}
    (f : Frame c k t) (hc : NoMonochromaticTriangle c) : ProperFive (rightSupport f) := by
  intro a ha b hb hab hcolor
  have hma : f.marked 15 ≠ f.right a := distinct_root_cells (f.marked_mem 15) (f.right_mem a) (by decide)
  have hmb : f.marked 15 ≠ f.right b := distinct_root_cells (f.marked_mem 15) (f.right_mem b) (by decide)
  have hma3 := (mem_filter.mp ha).2
  have hmb3 := (mem_filter.mp hb).2
  have he := f.right_edges a b hab
  change R4333.k15Twisted a b = 2 at hcolor
  rw [hcolor] at he
  exact hc (f.marked 15) (f.right a) (f.right b) ⟨hma,hmb,f.right.injective.ne hab⟩
    ⟨hma3.trans hmb3.symm,hmb3.trans he.symm⟩

def Strong (e : Fin 15 ≃ Fin 15) : Prop := ∀ a b, a ≠ b → T (e a) (e b) = T a b

theorem Strong.symm {e : Fin 15 ≃ Fin 15} (h : Strong e) : Strong e.symm := by
  intro a b hab
  have hh := h (e.symm a) (e.symm b) (e.symm.injective.ne hab)
  simpa only [Equiv.apply_symm_apply] using hh.symm

/-- A support automorphism changes coordinates of its entire physical block. -/
noncomputable def reindex {c : Host} {k : Nat} {t : Bool} (f : Frame c k t)
    (a b : Fin 15 ≃ Fin 15) (ha : Strong a) (hb : Strong b) : Frame c k t where
  root := f.root
  free := f.free
  left := a.symm.toEmbedding.trans f.left
  right := b.symm.toEmbedding.trans f.right
  marked := f.marked
  free_mem := f.free_mem
  left_mem i := f.left_mem (a.symm i)
  right_mem i := f.right_mem (b.symm i)
  marked_mem := f.marked_mem
  left_edges i j hij := by
    change c (f.left (a.symm i)) (f.left (a.symm j)) = _
    rw [f.left_edges _ _ (a.symm.injective.ne hij)]
    exact congrArg mPalette (Strong.symm ha i j hij)
  right_edges i j hij := by
    change c (f.right (b.symm i)) (f.right (b.symm j)) = _
    rw [f.right_edges _ _ (b.symm.injective.ne hij)]
    exact congrArg xPalette (Strong.symm hb i j hij)
  marked_edges := f.marked_edges

theorem leftSupport_reindex {c : Host} {k : Nat} {t : Bool} (f : Frame c k t)
    (a b : Fin 15 ≃ Fin 15) (ha : Strong a) (hb : Strong b) :
    leftSupport (reindex f a b ha hb) = (leftSupport f).image a := by
  ext i
  simp only [leftSupport,mem_filter,mem_univ,true_and,mem_image]
  change c (f.marked 15) (f.left (a.symm i)) = palette 3 ↔
    ∃ j, c (f.marked 15) (f.left j) = palette 3 ∧ a j = i
  constructor
  · intro h;exact ⟨a.symm i,h,by simp⟩
  · rintro ⟨j,h,rfl⟩;simpa using h

theorem rightSupport_reindex {c : Host} {k : Nat} {t : Bool} (f : Frame c k t)
    (a b : Fin 15 ≃ Fin 15) (ha : Strong a) (hb : Strong b) :
    rightSupport (reindex f a b ha hb) = (rightSupport f).image b := by
  ext i
  simp only [rightSupport,mem_filter,mem_univ,true_and,mem_image]
  change c (f.marked 15) (f.right (b.symm i)) = palette 3 ↔
    ∃ j, c (f.marked 15) (f.right j) = palette 3 ∧ b j = i
  constructor
  · intro h;exact ⟨b.symm i,h,by simp⟩
  · rintro ⟨j,h,rfl⟩;simpa using h

/-- All physical five-by-five supports normalize into the exact49 ordered
pairs of the archived census, without changing a single physical edge. -/
theorem physical_five_pair_cover {c : Host} {k : Nat} {t : Bool}
    (f : Frame c k t) (hc : NoMonochromaticTriangle c)
    (hl : (leftSupport f).card = 5) (hr : (rightSupport f).card = 5) :
    ∃ g : Frame c k t, ∃ i j : Fin representatives5.length,
      g.root = f.root ∧ g.marked = f.marked ∧ g.free = f.free ∧
      leftSupport g = representatives5.get i ∧ rightSupport g = representatives5.get j := by
  obtain ⟨s,hs,a,ha,has⟩ := five_support_cover (leftSupport f) hl (actual_left_support_avoids f hc)
  obtain ⟨u,hu,b,hb,hbu⟩ := five_support_cover (rightSupport f) hr (actual_right_support_avoids f hc)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hs
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hu
  refine ⟨reindex f a b ha hb,i,j,rfl,rfl,rfl,?_,?_⟩
  · rw [leftSupport_reindex,has,hi]
  · rw [rightSupport_reindex,hbu,hj]

/-- One global palette swap orders the support indices before any matrix
representative is chosen. Every diagonal case is retained. -/
theorem physical_TT_upper_pair_cover {c : Host} {k : Nat} {t : Bool}
    (f : Frame c k t) (hc : NoMonochromaticTriangle c)
    (hl : (leftSupport f).card = 5) (hr : (rightSupport f).card = 5) :
    ∃ changed : Bool, ∃ g : Frame (if changed then swappedHost c else c) k t,
    ∃ i j : Fin representatives5.length, i ≤ j ∧
      g.root = f.root ∧ g.marked 15 = f.marked 15 ∧
      leftSupport g = representatives5.get i ∧ rightSupport g = representatives5.get j ∧
      NoMonochromaticTriangle (if changed then swappedHost c else c) ∧
      H (if changed then swappedHost c else c) f.root = H c f.root ∧
      W (if changed then swappedHost c else c) f.root = W c f.root := by
  obtain ⟨g,i,j,hroot,hmark,hfree,hleft,hright⟩ := physical_five_pair_cover f hc hl hr
  by_cases hij : i ≤ j
  · refine ⟨false,g,i,j,hij,hroot,?_,hleft,hright,hc,rfl,rfl⟩
    rw [hmark]
  · refine ⟨true,g.exchange,j,i,le_of_lt (lt_of_not_ge hij),hroot,?_,?_,?_,
      swappedHost_good c hc,swappedHost_H c f.root,swappedHost_W c f.root⟩
    · rw [exchange_mark,hmark]
    · exact (leftSupport_exchange g).trans hright
    · exact (rightSupport_exchange g).trans hleft

#print axioms physical_five_pair_cover
#print axioms physical_TT_upper_pair_cover
#check physical_TT_upper_pair_cover
end PricingABD.SupportTransport
