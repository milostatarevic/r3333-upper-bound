import UniformK60.HostNormalizationRoot

/-! Name a C2 root in the raw brace coordinates: two low colors followed
by its16-color and15-color. Only the global palette changes here. -/
set_option autoImplicit false
namespace UniformK60.BalancedRawRoot
open Ramsey61 UniformK60.Physical UniformK60.HostNormalization

def RawCaps (c : Host) : Prop := ∀ v : Vertex,∀ q : Color,
  colorDegree c (palette q) v ≤ if q.val<2 then 14 else 16

def rawDegree : Color → Nat := ![14,14,16,15]
def rawToNamed : Color → Color := ![2,3,1,0]

def rotate : Equiv.Perm FourColor where
  toFun a := (!a.1,xor a.1 a.2)
  invFun a := (!a.1,xor (!a.1) a.2)
  left_inv := by decide
  right_inv := by decide

theorem rotate_palette : ∀ q,rotate (palette q)=palette (rawToNamed q) := by decide

theorem normalized_root (c : Host) (hc : NoMonochromaticTriangle c)
    (hn : NamedCaps c) (r : Vertex) (hw : W c r=31) :
    ∃ σ : Equiv.Perm FourColor,
      NoMonochromaticTriangle (relabel c (Equiv.refl _) σ) ∧
      RawCaps (relabel c (Equiv.refl _) σ) ∧
      ∀ q : Color,colorDegree (relabel c (Equiv.refl _) σ) (palette q) r=rawDegree q := by
  obtain ⟨c1,σ,hσ,hd⟩ := named_root_orientation c hn r
  have hW := canonical_degrees_W (relabel c (Equiv.refl _) σ) r c1 (by
    intro q
    rw [relabel_degree]
    exact hd q)
  rw [relabel_W] at hW
  have hfalse : c1=false := by
    cases c1
    · rfl
    · simp only [ite_true,Equiv.refl_apply] at hW
      omega
  subst c1
  let τ := rotate.trans σ
  refine ⟨τ,relabel_noMono c hc _ _,?_,?_⟩
  · intro v q
    have hn' := relabel_named_caps c hn (Equiv.refl _) σ hσ v (rawToNamed q)
    rw [relabel_degree] at hn' ⊢
    change colorDegree c (σ (rotate (palette q))) v≤_
    rw [rotate_palette]
    fin_cases q <;> simpa [rawToNamed] using hn'
  · intro q
    rw [relabel_degree]
    change colorDegree c (σ (rotate (palette q))) r=rawDegree q
    rw [rotate_palette,hd]
    fin_cases q <;> rfl

#print axioms normalized_root
end UniformK60.BalancedRawRoot
