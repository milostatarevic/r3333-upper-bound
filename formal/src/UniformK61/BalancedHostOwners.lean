import UniformK61.BalancedHostNormalization

set_option autoImplicit false
namespace UniformK61.BalancedHost
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open PricingIntegration.BActualFrame

def swapVertexFn (v : Vertex) : Vertex :=
  if h : 1 ≤ v.val ∧ v.val ≤ 16 then ⟨v.val+16,by omega⟩
  else if h : 17 ≤ v.val ∧ v.val ≤ 32 then ⟨v.val-16,by omega⟩ else v

theorem swapVertexFn_involutive : Function.Involutive swapVertexFn := by
  change ∀ v, swapVertexFn (swapVertexFn v) = v
  decide

def swapVertices : Vertex ≃ Vertex :=
  ⟨swapVertexFn,swapVertexFn,swapVertexFn_involutive,swapVertexFn_involutive⟩

def swapColors : FourColor ≃ FourColor := Equiv.swap (palette 0) (palette 1)
def swapColorIndex : Color ≃ Color := Equiv.swap 0 1

def swapNonroot (v : Fin 60) : Fin 60 :=
  if h : v.val < 16 then ⟨v.val+16,by omega⟩
  else if h : v.val < 32 then ⟨v.val-16,by omega⟩ else v

theorem swap_root : swapVertices 0 = 0 := rfl
theorem swap_x : ∀ i, swapVertices (xVertex i) = yVertex i := by decide
theorem swap_y : ∀ i, swapVertices (yVertex i) = xVertex i := by decide
theorem swap_vertex_nonroot : ∀ v,
    swapVertices (BalancedHost.vertex v) = BalancedHost.vertex (swapNonroot v) := by decide
theorem swap_spoke_palette : ∀ v,
    swapColors.symm (palette (BalancedHost.rootColor (swapNonroot v))) =
      palette (BalancedHost.rootColor v) := by decide
theorem swap_palette : ∀ q, swapColors (palette q) = palette (swapColorIndex q) := by decide
theorem swap_target : ∀ q,
    BalancedHost.target (swapColorIndex q) = BalancedHost.target q := by decide
theorem swap_foreign0 : ∀ q,
    swapColors.symm (palette (foreign 1 q)) = palette (foreign 0 q) := by decide
theorem swap_foreign1 : ∀ q,
    swapColors.symm (palette (foreign 0 q)) = palette (foreign 1 q) := by decide

def exchanged (c : Host) : Host := relabel c swapVertices swapColors

theorem exchanged_good (c : Host) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (exchanged c) := relabel_noMono c hc _ _

/-- Exchange both complete high cells and the two high color names in one
physical host. Low cells and their color names remain fixed. -/
theorem exchanged_normalized {c : Host} {tx ty : Bool} (h : Normalized c tx ty) :
    Normalized (exchanged c) ty tx := by
  refine ⟨?_,?_,?_,?_⟩
  · intro v q
    rw [exchanged,relabel_degree,swap_palette,h.named,swap_target]
  · intro v
    change swapColors.symm (c (swapVertices 0) (swapVertices (BalancedHost.vertex v))) = _
    rw [swap_root,swap_vertex_nonroot,h.spokes,swap_spoke_palette]
  · intro i j hij
    change swapColors.symm (c (swapVertices (xVertex i)) (swapVertices (xVertex j))) = _
    rw [swap_x,swap_x,h.right_template i j hij,swap_foreign0]
  · intro i j hij
    change swapColors.symm (c (swapVertices (yVertex i)) (swapVertices (yVertex j))) = _
    rw [swap_y,swap_y,h.left_template i j hij,swap_foreign1]

/-- Complete three-owner boundary. TU is carried to UT by the explicit
whole-host exchange; no local recoloring of overlapping scopes is used. -/
theorem uniform_to_three_owners (c : Host) (hc : NoMonochromaticTriangle c)
    (hu : UniformCommonHighPair c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧ ∃ o : Owner, Normalized d o.left o.right := by
  obtain ⟨d,hd,tx,ty,h⟩ := uniform_to_four_owners c hc hu
  cases tx <;> cases ty
  · exact ⟨d,hd,.uu,h⟩
  · exact ⟨d,hd,.ut,h⟩
  · exact ⟨exchanged d,exchanged_good d hd,.ut,exchanged_normalized h⟩
  · exact ⟨d,hd,.tt,h⟩

#print axioms uniform_to_three_owners
#print axioms exchanged_normalized
end UniformK61.BalancedHost
