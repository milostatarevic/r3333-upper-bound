import UniformK60.CommonPairAdmission
import UniformK60.HostNormalization
import PricingABD.TTExchange

set_option autoImplicit false
namespace UniformK60.CommonExchange
open UniformK60.ClassificationGeometry
open Ramsey61 UniformK60.Physical UniformK60.ClassificationAdapter
open UniformK60.HostNormalization PricingABD PricingABD.ABLayout
open UniformK60.PhysicalHelpers UniformK60.ClassificationSupports
open UniformK60.CommonBlocks UniformK60.CommonPairAdmission CompletionC.NativeMatrices

abbrev colorSwap := PricingABD.TTExchange.colorSwap

def swappedHost (c : Host) : Host := relabel c (Equiv.refl _) colorSwap
@[simp] theorem swappedHost_apply (c : Host) (a b : Vertex) :
    swappedHost c a b = colorSwap.symm (c a b) := rfl

theorem swappedHost_good (c : Host) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (swappedHost c) := relabel_noMono c hc _ _

theorem swappedHost_mem (c : Host) (q : FourColor) (r u : Vertex) :
    u ∈ colorNeighborhood (swappedHost c) q r ↔
      u ∈ colorNeighborhood c (colorSwap q) r := by
  simp [mem_colorNeighborhood,swappedHost_apply,Equiv.symm_apply_eq]

private theorem swap_pal12 (a : Fin 3) :
    colorSwap.symm (foreignEquiv 2 a).val = (foreignEquiv 1 a).val := by
  fin_cases a <;> rfl
private theorem swap_pal21 (a : Fin 3) :
    colorSwap.symm (foreignEquiv 1 a).val = (foreignEquiv 2 a).val := by
  fin_cases a <;> rfl

def swapTypes (t : Types) : Types := ⟨t.right,t.left,t.marked⟩

noncomputable def exchangeLeft {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) :
    PhysicalNeighborhoodMap (swappedHost c) b.root (palette 1)
      (R4333.k15Template t.right) where
  vertex := b.right.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (b.right.mem_neighborhood i)
  covers_neighborhood v hv := b.right.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 1
  map_color a d had := by
    change colorSwap.symm (c (b.right.vertex a) (b.right.vertex d)) = _
    rw [b.right.map_color a d had,b.right_palette,swap_pal12]
    cases t.right <;> rfl

noncomputable def exchangeRight {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) :
    PhysicalNeighborhoodMap (swappedHost c) b.root (palette 2)
      (R4333.k15Template t.left) where
  vertex := b.left.vertex
  mem_neighborhood i := (swappedHost_mem _ _ _ _).mpr (b.left.mem_neighborhood i)
  covers_neighborhood v hv := b.left.covers_neighborhood v ((swappedHost_mem _ _ _ _).mp hv)
  colors := foreignEquiv 2
  map_color a d had := by
    change colorSwap.symm (c (b.left.vertex a) (b.left.vertex d)) = _
    rw [b.left.map_color a d had,b.left_palette,swap_pal21]
    cases t.left <;> rfl

/-- One global palette exchange of an actual host. No marked-cell template
is needed for the support-word normalization. -/
noncomputable def exchange {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) : Blocks (swappedHost c) ⟨.D,five⟩ (swapTypes t) where
  root := b.root
  mark := b.mark
  free := b.free
  left := exchangeLeft b
  right := exchangeRight b
  mark_mem := (swappedHost_mem _ _ _ _).mpr b.mark_mem
  free_mem i := (swappedHost_mem _ _ _ _).mpr (b.free_mem i)
  left_palette := rfl
  right_palette := rfl
  marked_high := by
    change 15 ≤ colorDegree (relabel c (Equiv.refl _) colorSwap) (palette 3) b.mark
    rw [relabel_degree]
    exact b.marked_high
  free_own i := by
    rw [swappedHost_apply,b.free_own]
    rfl
  free_exact v := by
    have h : attachingSupport (swappedHost c) b.root (palette 3) b.mark (palette 0) =
        attachingSupport c b.root (palette 3) b.mark (palette 0) := by
      ext u
      simp only [UniformK60.ClassificationGeometry.attachingSupport,Finset.mem_inter,swappedHost_mem]
      rfl
    rw [h]
    exact b.free_exact v

@[simp] theorem exchange_root {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) : (exchange b).root = b.root := rfl
@[simp] theorem exchange_mark {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) : (exchange b).mark = b.mark := rfl
@[simp] theorem exchange_left {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) (i : Fin 15) :
    (exchange b).left.vertex i = b.right.vertex i := rfl
@[simp] theorem exchange_right {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) (i : Fin 15) :
    (exchange b).right.vertex i = b.left.vertex i := rfl

theorem exchange_left_support {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) :
    support (side:=false) (exchange b).left (exchange b).mark =
      support (side:=true) b.right b.mark := by
  change (Finset.univ.filter fun i : Fin 15 => swappedHost c b.mark (b.right.vertex i)=palette 3) =
    (Finset.univ.filter fun i : Fin 15 => c b.mark (b.right.vertex i)=palette 3)
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,swappedHost_apply]
  rw [Equiv.symm_apply_eq]
  rfl

theorem exchange_right_support {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) :
    support (side:=true) (exchange b).right (exchange b).mark =
      support (side:=false) b.left b.mark := by
  change (Finset.univ.filter fun i : Fin 15 => swappedHost c b.mark (b.left.vertex i)=palette 3) =
    (Finset.univ.filter fun i : Fin 15 => c b.mark (b.left.vertex i)=palette 3)
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,swappedHost_apply]
  rw [Equiv.symm_apply_eq]
  rfl

def swapShape : Shape → Shape
 | .freeFour => .freeFour | .leftFour => .rightFour
 | .rightFour => .leftFour | .allFive => .allFive

theorem exchange_record {c : Host} {five : Bool} {t : Types}
    (b : Blocks c ⟨.D,five⟩ t) (s : Shape) :
    sourceRecord (exchange b) (swapShape s) =
      PricingIntegration.PairAdmission.exchange (sourceRecord b s) := by
  unfold sourceRecord PricingIntegration.PairAdmission.exchange
  rw [exchange_left_support,exchange_right_support]
  cases s <;> rfl

/-- Complete actual-host support-pair admission, including the sole census
exchange. The physical root and mark survive this global recoloring. -/
theorem actual_pair_admitted {c : Host} {l : Layout} {t : Types} (b : Blocks c l t)
    (hc : NoMonochromaticTriangle c) (sl sr : Bool)
    (hn : UniformK60.CommonSupportNormalization.Normalized b sl sr) (ho : CommonOwner l t) :
    ∃ σ : FourColor ≃ FourColor, let d := relabel c (Equiv.refl _) σ
    NoMonochromaticTriangle d ∧ (σ = Equiv.refl _ ∨ σ = colorSwap) ∧ ∃ u : Types, ∃ z : Blocks d l u,
      u=t ∧ z.root=b.root ∧ z.mark=b.mark ∧
      ∃ s : Shape, freeSize l=s.free ∧ ∃ p : Fin 737,
        PricingIntegration.PairAdmission.retained p=sourceRecord z s := by
  obtain ⟨s,hf,hl,hr,p,hp,hcase⟩ := normalized_admitted b hc sl sr hn ho
  rcases hcase with he | ⟨hD,hL,hR,he⟩
  · exact ⟨Equiv.refl _,hc,Or.inl rfl,t,b,rfl,rfl,rfl,s,hf,p,he⟩
  · rcases l with ⟨profile,five⟩
    cases hD
    have ht : swapTypes t=t := by cases t with | mk a d q => simp_all [swapTypes]
    refine ⟨colorSwap,swappedHost_good c hc,Or.inr rfl,swapTypes t,exchange b,ht,rfl,rfl,
      swapShape s,?_,p,?_⟩
    · cases s <;> exact hf
    · exact he.trans (exchange_record b s).symm

#print axioms actual_pair_admitted
end UniformK60.CommonExchange
