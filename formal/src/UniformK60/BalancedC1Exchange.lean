import UniformK60.BalancedC1Normalize

set_option autoImplicit false
namespace UniformK60.BalancedC1Exchange
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.HostNormalization UniformK60.BalancedHost

def swapMap (v : Vertex) : Vertex :=
  if h : 1≤v.val ∧ v.val≤16 then ⟨v.val+16,by omega⟩
  else if h : 17≤v.val ∧ v.val≤32 then ⟨v.val-16,by omega⟩ else v

theorem swap_involution : ∀ v,swapMap (swapMap v)=v := by decide

def swapVertices : Vertex ≃ Vertex where
  toFun := swapMap
  invFun := swapMap
  left_inv := swap_involution
  right_inv := swap_involution

def swapPalette : Equiv.Perm FourColor := Equiv.swap (palette 0) (palette 1)

theorem root_fixed : swapVertices 0=0 := by rfl
theorem swaps_x : ∀ i : Fin 16,swapVertices (xVertex true i)=yVertex true i := by decide
theorem swaps_y : ∀ i : Fin 16,swapVertices (yVertex true i)=xVertex true i := by decide
theorem preserves_pair : PairPreserving swapPalette := by unfold PairPreserving;decide
theorem swaps_cells : ∀ v : Vertex,
    Option.map swapPalette.symm (canonicalCell true (swapVertices v))=canonicalCell true v := by decide
theorem swaps_left_palette : ∀ q : Fin 3,
    swapPalette.symm (palette (foreign 1 q))=palette (foreign 0 q) := by decide
theorem swaps_right_palette : ∀ q : Fin 3,
    swapPalette.symm (palette (foreign 0 q))=palette (foreign 1 q) := by decide

theorem normalized_swap {c : Host} {o : Owner} (h : Normalized true c o) :
    Normalized true (relabel c swapVertices swapPalette) (o.2,o.1) := by
  refine ⟨relabel_named_caps c h.caps _ _ preserves_pair,?_,?_,?_⟩
  · intro v
    by_cases hv : v=0
    · subst v
      rfl
    have he : swapVertices v≠0 := by
      simpa only [root_fixed] using swapVertices.injective.ne hv
    have hs := congrArg (Option.map swapPalette.symm) (h.spokes (swapVertices v))
    simp only [rootCell,if_neg he,Equiv.refl_symm,Equiv.refl_apply,Option.map_some] at hs
    change (if v=0 then none else some (swapPalette.symm (c (swapVertices 0) (swapVertices v))))=_
    rw [if_neg hv,root_fixed,hs,swaps_cells]
  · intro a b hab
    change swapPalette.symm (c (swapVertices (xVertex true a)) (swapVertices (xVertex true b)))=_
    rw [swaps_x,swaps_x,h.right_template a b hab,swaps_left_palette]
    rfl
  · intro a b hab
    change swapPalette.symm (c (swapVertices (yVertex true a)) (swapVertices (yVertex true b)))=_
    rw [swaps_y,swaps_y,h.left_template a b hab,swaps_right_palette]
    rfl

/-- Only UU,UT,TT are required for two equal-sized complete critical cells. -/
theorem ordered {c : Host} {o : Owner} (hc : NoMonochromaticTriangle c)
    (h : Normalized true c o) (hall : ∀ v,W c v=32) :
    ∃ d : Host,∃ t : Owner,NoMonochromaticTriangle d ∧ Normalized true d t ∧
      (t=(false,false) ∨ t=(false,true) ∨ t=(true,true)) ∧
      (∀ v,W d v=32) := by
  rcases o with ⟨tx,ty⟩
  cases tx <;> cases ty
  · exact ⟨c,(false,false),hc,h,Or.inl rfl,hall⟩
  · exact ⟨c,(false,true),hc,h,Or.inr (Or.inl rfl),hall⟩
  · refine ⟨relabel c swapVertices swapPalette,(false,true),
      relabel_noMono c hc _ _,normalized_swap h,Or.inr (Or.inl rfl),?_⟩
    intro v
    rw [relabel_W]
    exact hall _
  · exact ⟨c,(true,true),hc,h,Or.inr (Or.inr rfl),hall⟩

#print axioms normalized_swap
end UniformK60.BalancedC1Exchange
