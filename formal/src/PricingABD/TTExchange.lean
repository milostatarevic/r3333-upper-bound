import PricingABD.PaletteSymmetry
import Ramsey61.CPhysicalNormalization
import Ramsey61.ClassificationAdapter

namespace PricingABD.TTExchange
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization

/-- The one global palette exchange used by the TT cover. -/
def colorSwap : FourColor ≃ FourColor := Equiv.prodComm Bool Bool

def localSwap : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

def qPalette (a : Fin 3) : FourColor := palette (Fin.castLE (by decide) a)
def mPalette : Fin 3 → FourColor := ![palette 0,palette 2,palette 3]
def xPalette : Fin 3 → FourColor := ![palette 0,palette 1,palette 3]

@[simp] theorem colorSwap_m (a : Fin 3) : colorSwap.symm (mPalette a) = xPalette a := by fin_cases a <;> rfl
@[simp] theorem colorSwap_x (a : Fin 3) : colorSwap.symm (xPalette a) = mPalette a := by fin_cases a <;> rfl
@[simp] theorem colorSwap_q (a : Fin 3) : colorSwap.symm (qPalette (localSwap a)) = qPalette a := by fin_cases a <;> decide

/-- Apply the checked palette lift, then use actual template transitivity to fix15. -/
noncomputable def markedQMap (t : Bool) : Fin 16 ≃ Fin 16 :=
  let psi := R4333.k16PaletteVertexEquiv t 1
  let before := psi.symm 15
  (R4333.k16TemplateToLastEquiv t before).symm.trans psi

theorem markedQMap_fixes (t : Bool) : markedQMap t 15 = 15 := by
  let psi := R4333.k16PaletteVertexEquiv t 1
  let before := psi.symm 15
  let alpha := R4333.k16TemplateToLastEquiv t before
  have h : alpha before = 15 := R4333.k16TemplateToLastMap_deleted t before
  have ha : alpha.symm 15 = before := by rw [←h]; simp
  change psi (alpha.symm 15) = 15
  rw [ha]
  exact psi.apply_symm_apply 15

theorem markedQMap_preserves (t : Bool) (a b : Fin 16) (h : a ≠ b) :
    R4333.k16Template t (markedQMap t a) (markedQMap t b) =
      localSwap (R4333.k16Template t a b) := by
  let psi := R4333.k16PaletteVertexEquiv t 1
  let before := psi.symm 15
  let alpha := R4333.k16TemplateToLastEquiv t before
  have hn : alpha.symm a ≠ alpha.symm b := alpha.symm.injective.ne h
  have ha := R4333.k16TemplateToLastMap_preserves t before (alpha.symm a) (alpha.symm b) hn
  change R4333.k16Template t (alpha.symm a) (alpha.symm b) =
      R4333.k16Template t (alpha (alpha.symm a)) (alpha (alpha.symm b)) at ha
  simp only [Equiv.apply_symm_apply] at ha
  change R4333.k16Template t (psi (alpha.symm a)) (psi (alpha.symm b)) = _
  rw [R4333.k16PaletteVertexEquiv_apply,R4333.k16PaletteVertexEquiv_apply,
    R4333.k16PaletteVertexMap_preserves t 1 _ _ hn,ha]
  have hh : R4333.criticalPaletteColorMap 1 = localSwap := by funext q;fin_cases q <;> decide
  rw [hh]

/-- All embeddings point into one original61-vertex coloring. No extra vertices or glued colorings. -/
structure Frame (c : Host) (k : Nat) (qtype : Bool) where
  root : Fin 61
  free : Fin k ↪ Fin 61
  left : Fin 15 ↪ Fin 61
  right : Fin 15 ↪ Fin 61
  marked : Fin 16 ↪ Fin 61
  free_mem : ∀ i, free i ∈ colorNeighborhood c (palette 0) root
  left_mem : ∀ i, left i ∈ colorNeighborhood c (palette 1) root
  right_mem : ∀ i, right i ∈ colorNeighborhood c (palette 2) root
  marked_mem : ∀ i, marked i ∈ colorNeighborhood c (palette 3) root
  left_edges : ∀ a b, a ≠ b → c (left a) (left b) = mPalette (R4333.k15Twisted a b)
  right_edges : ∀ a b, a ≠ b → c (right a) (right b) = xPalette (R4333.k15Twisted a b)
  marked_edges : ∀ a b, a ≠ b → c (marked a) (marked b) = qPalette (R4333.k16Template qtype a b)

/-- The same physical graph after one global1↔2 color change. -/
def swappedHost (c : Host) : Host := relabel c (Equiv.refl _) colorSwap

@[simp] theorem swappedHost_apply (c : Host) (a b : Fin 61) :
    swappedHost c a b = colorSwap.symm (c a b) := rfl

theorem swappedHost_good (c : Host) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (swappedHost c) := relabel_noMono c hc _ _

@[simp] theorem swappedHost_H (c : Host) (r : Fin 61) : H (swappedHost c) r = H c r := relabel_H c _ _ _
@[simp] theorem swappedHost_W (c : Host) (r : Fin 61) : W (swappedHost c) r = W c r := relabel_W c _ _ _

theorem swappedHost_mem (c : Host) (q : FourColor) (r u : Fin 61) :
    u ∈ colorNeighborhood (swappedHost c) q r ↔ u ∈ colorNeighborhood c (colorSwap q) r := by
  simp [mem_colorNeighborhood,swappedHost_apply,Equiv.symm_apply_eq]

/-- Canonical blocks are restored by exchanging the two foreign T15 embeddings
and the whole Q map, including every edge incident to Q. -/
noncomputable def Frame.exchange {c : Host} {k : Nat} {qtype : Bool}
    (f : Frame c k qtype) : Frame (swappedHost c) k qtype where
  root := f.root
  free := f.free
  left := f.right
  right := f.left
  marked := (markedQMap qtype).toEmbedding.trans f.marked
  free_mem i := (swappedHost_mem _ _ _ _).mpr (f.free_mem i)
  left_mem i := (swappedHost_mem _ _ _ _).mpr (f.right_mem i)
  right_mem i := (swappedHost_mem _ _ _ _).mpr (f.left_mem i)
  marked_mem i := (swappedHost_mem _ _ _ _).mpr (f.marked_mem (markedQMap qtype i))
  left_edges a b h := by rw [swappedHost_apply,f.right_edges a b h,colorSwap_x]
  right_edges a b h := by rw [swappedHost_apply,f.left_edges a b h,colorSwap_m]
  marked_edges a b h := by
    change colorSwap.symm (c (f.marked (markedQMap qtype a)) (f.marked (markedQMap qtype b))) = _
    rw [f.marked_edges _ _ ((markedQMap qtype).injective.ne h),markedQMap_preserves _ _ _ h,colorSwap_q]

@[simp] theorem exchange_mark {c : Host} {k : Nat} {qtype : Bool}
    (f : Frame c k qtype) : f.exchange.marked 15 = f.marked 15 := by
  change f.marked (markedQMap qtype 15) = f.marked 15
  rw [markedQMap_fixes]

/-- The exact physical selected color3 supports in the foreign coordinates. -/
def leftSupport {c : Host} {k : Nat} {qtype : Bool} (f : Frame c k qtype) : Finset (Fin 15) :=
  Finset.univ.filter fun i => c (f.marked 15) (f.left i) = palette 3

def rightSupport {c : Host} {k : Nat} {qtype : Bool} (f : Frame c k qtype) : Finset (Fin 15) :=
  Finset.univ.filter fun i => c (f.marked 15) (f.right i) = palette 3

theorem leftSupport_exchange {c : Host} {k : Nat} {qtype : Bool} (f : Frame c k qtype) :
    leftSupport f.exchange = rightSupport f := by
  ext i
  simp only [leftSupport,rightSupport,Finset.mem_filter,Finset.mem_univ,true_and,exchange_mark]
  change colorSwap.symm (c (f.marked 15) (f.right i)) = palette 3 ↔ _
  rw [Equiv.symm_apply_eq]
  rfl

theorem rightSupport_exchange {c : Host} {k : Nat} {qtype : Bool} (f : Frame c k qtype) :
    rightSupport f.exchange = leftSupport f := by
  ext i
  simp only [leftSupport,rightSupport,Finset.mem_filter,Finset.mem_univ,true_and,exchange_mark]
  change colorSwap.symm (c (f.marked 15) (f.left i)) = palette 3 ↔ _
  rw [Equiv.symm_apply_eq]
  rfl

/-- Exact supports swap; H, W, root, marked vertex and Q type stay fixed. -/
theorem physical_TT_exchange {c : Host} {k : Nat} {qtype : Bool}
    (f : Frame c k qtype) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (swappedHost c) ∧
    H (swappedHost c) f.root = H c f.root ∧ W (swappedHost c) f.root = W c f.root ∧
    f.exchange.root = f.root ∧ f.exchange.marked 15 = f.marked 15 ∧
    leftSupport f.exchange = rightSupport f ∧ rightSupport f.exchange = leftSupport f := by
  exact ⟨swappedHost_good c hc,swappedHost_H c f.root,swappedHost_W c f.root,
    rfl,exchange_mark f,leftSupport_exchange f,rightSupport_exchange f⟩

#print axioms markedQMap_preserves
#print axioms physical_TT_exchange
#check physical_TT_exchange
end PricingABD.TTExchange
