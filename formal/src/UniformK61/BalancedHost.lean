import UniformK61.Physical
import UniformK61.HostNormalization
import Ramsey61.Uniform
import PricingIntegration.BActualFrame

/-! Canonical physical layout for the balanced complete-host formulas. -/

set_option autoImplicit false
namespace UniformK61.BalancedHost
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CPhysicalNormalization
open Ramsey61.ClassificationAdapter PricingIntegration.BActualFrame
open PricingIntegration.FixedPhysicalNeighborhood

/-- The sixty nonroot vertices, in physical order. -/
def vertex (v : Fin 60) : Vertex := ⟨v.val+1,by omega⟩

/-- The common named color-degree vector. -/
def target (q : Color) : Nat := if q.val < 2 then 16 else 14

/-- The four consecutive root cells have sizes16,16,14,14. -/
def rootColor (v : Fin 60) : Color :=
  if v.val < 16 then 0 else if v.val < 32 then 1 else if v.val < 46 then 2 else 3

theorem vertex_ne_zero (v : Fin 60) : vertex v ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp only [vertex,Fin.val_zero] at this
  omega

def Named (c : Host) : Prop := ∀ v q, colorDegree c (palette q) v = BalancedHost.target q
def Spokes (c : Host) : Prop := ∀ v : Fin 60,
  c 0 (BalancedHost.vertex v) = palette (BalancedHost.rootColor v)

def xVertex (i : Fin 16) : Vertex := ⟨i.val+1,by omega⟩
def yVertex (i : Fin 16) : Vertex := ⟨i.val+17,by omega⟩
def pVertex (i : Fin 14) : Vertex := ⟨i.val+33,by omega⟩
def qVertex (i : Fin 14) : Vertex := ⟨i.val+47,by omega⟩

def TemplateAt (c : Host) (embed : Fin 16 → Vertex) (omitted : Color) (t : Bool) : Prop :=
  ∀ i j, i ≠ j → c (embed i) (embed j) = palette (foreign omitted (R4333.k16Template t i j))

structure Normalized (c : Host) (left right : Bool) : Prop where
  named : Named c
  spokes : Spokes c
  left_template : TemplateAt c xVertex 0 left
  right_template : TemplateAt c yVertex 1 right

inductive Owner where | uu | ut | tt deriving DecidableEq, Fintype

def Owner.left : Owner → Bool | .uu => false | .ut => false | .tt => true
def Owner.right : Owner → Bool | .uu => false | .ut => true | .tt => true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem high_pair_palette : ∀ high : Finset FourColor, high.card = 2 →
    ∃ σ : Equiv.Perm FourColor, ∀ q : Color, (σ (palette q) ∈ high ↔ q.val < 2) := by decide

set_option maxRecDepth 10000 in
theorem canonical_spoke : ∀ v : Fin 60,
    canonicalCell (BalancedHost.vertex v) =
      some (palette (BalancedHost.rootColor v)) := by decide

/-- The common named degree vector and all60 root spokes arise by one
whole-host relabeling. No root-template or local embedding premise is used. -/
theorem uniform_to_named_spokes (c : Host) (hc : NoMonochromaticTriangle c)
    (hu : UniformCommonHighPair c) :
    ∃ d : Host, NoMonochromaticTriangle d ∧ Named d ∧ Spokes d := by
  classical
  obtain ⟨high,hcard,hdegrees⟩ := hu
  obtain ⟨σ,hσ⟩ := high_pair_palette high hcard
  have hd (v : Vertex) (q : Color) :
      colorDegree c (σ (palette q)) v = BalancedHost.target q := by
    rw [hdegrees]
    simp only [BalancedHost.target,hσ q]
  obtain ⟨e,he0,he⟩ := exists_root_cell_equiv c 0 σ (hd 0)
  let d := relabel c e σ
  refine ⟨d,relabel_noMono c hc e σ,?_,?_⟩
  · intro v q
    exact (relabel_degree c e σ (palette q) v).trans (hd (e v) q)
  · intro v
    have hm : e (BalancedHost.vertex v) ∈
        colorNeighborhood c (σ (palette (BalancedHost.rootColor v))) 0 := by
      apply (rootCell_some c 0 _ σ _).mp
      rw [he,canonical_spoke]
    have hedge := (mem_colorNeighborhood _ _ _ _).mp hm
    change σ.symm (c (e 0) (e (BalancedHost.vertex v))) = _
    rw [he0,hedge.2,Equiv.symm_apply_apply]

theorem spoke_x (c : Host) (h : Spokes c) (i : Fin 16) : c 0 (xVertex i) = palette 0 := by
  have hh := h ⟨i.val,by omega⟩
  simpa [BalancedHost.vertex,BalancedHost.rootColor,xVertex,i.isLt] using hh

theorem spoke_y (c : Host) (h : Spokes c) (i : Fin 16) : c 0 (yVertex i) = palette 1 := by
  have hh := h ⟨i.val+16,by omega⟩
  have h0 : ¬i.val+16 < 16 := by omega
  have h1 : i.val+16 < 32 := by omega
  simpa [BalancedHost.vertex,BalancedHost.rootColor,yVertex,h0,h1,Nat.add_assoc] using hh

theorem spoke_p (c : Host) (h : Spokes c) (i : Fin 14) : c 0 (pVertex i) = palette 2 := by
  have hh := h ⟨i.val+32,by omega⟩
  have h0 : ¬i.val+32 < 16 := by omega
  have h1 : ¬i.val+32 < 32 := by omega
  have h2 : i.val+32 < 46 := by omega
  simpa [BalancedHost.vertex,BalancedHost.rootColor,pVertex,h0,h1,h2,Nat.add_assoc] using hh

theorem spoke_q (c : Host) (h : Spokes c) (i : Fin 14) : c 0 (qVertex i) = palette 3 := by
  have hh := h ⟨i.val+46,by omega⟩
  have h0 : ¬i.val+46 < 16 := by omega
  have h1 : ¬i.val+46 < 32 := by omega
  have h2 : ¬i.val+46 < 46 := by omega
  simpa [BalancedHost.vertex,BalancedHost.rootColor,qVertex,h0,h1,h2,Nat.add_assoc] using hh

#print axioms uniform_to_named_spokes
end UniformK61.BalancedHost
