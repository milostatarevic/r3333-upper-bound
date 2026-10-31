import UniformK60.HostNormalizationPair
import UniformK60.BalancedVisible
import UniformK61.BalancedAnchorSupportFinite

/-! The two canonical balanced root layouts, on the same sixty vertices.
Global caps are generic and admit all four deficiency colors. -/
set_option autoImplicit false
namespace UniformK60.BalancedHost
open Ramsey61 UniformK60.Physical UniformK60.PhysicalHelpers
open UniformK60.HostNormalization
open UniformK61.BalancedEncodingData

abbrev Owner := Bool × Bool
abbrev leftKind (o : Owner) := o.1
abbrev rightKind (o : Owner) := o.2

theorem firstSize_le (c1 : Bool) : firstSize c1 ≤ 16 := by cases c1 <;> decide

def xVertex (c1 : Bool) (i : Fin (firstSize c1)) : Vertex := ⟨i.val+1,by
  have := firstSize_le c1
  have := i.isLt
  omega⟩
def yVertex (c1 : Bool) (i : Fin 16) : Vertex := ⟨i.val+firstSize c1+1,by
  have := firstSize_le c1
  omega⟩

def Spokes (c1 : Bool) (c : Host) : Prop :=
  ∀ v, rootCell c 0 (Equiv.refl _) v = canonicalCell c1 v

def TemplateAt {n : Nat} (hn : n ≤ 16) (c : Host)
    (embed : Fin n → Vertex) (omitted : Color) (kind : Bool) : Prop :=
  ∀ i j, i ≠ j → c (embed i) (embed j) =
    palette (foreign omitted (R4333.k16Template kind (Fin.castLE hn i) (Fin.castLE hn j)))

structure Normalized (c1 : Bool) (c : Host) (o : Owner) : Prop where
  caps : NamedCaps c
  spokes : Spokes c1 c
  left_template : TemplateAt (firstSize_le c1) c (xVertex c1) 0 o.1
  right_template : TemplateAt (by decide) c (yVertex c1) 1 o.2

abbrev Scope (c1 : Bool) := Fin (firstSize c1) ⊕ Fin 16

def ownSize {c1 : Bool} : Scope c1 → Nat | .inl _ => firstSize c1 | .inr _ => 16
def otherSize {c1 : Bool} : Scope c1 → Nat | .inl _ => 16 | .inr _ => firstSize c1

theorem own_le {c1 : Bool} (s : Scope c1) : ownSize s ≤ 16 := by
  cases s <;> simp only [ownSize]
  · exact firstSize_le c1
  · decide

theorem other_le {c1 : Bool} (s : Scope c1) : otherSize s ≤ 16 := by
  cases s <;> simp only [otherSize]
  · decide
  · exact firstSize_le c1

def ownVertex {c1 : Bool} : (s : Scope c1) → Fin (ownSize s) → Vertex
  | .inl _, i => xVertex c1 i
  | .inr _, i => yVertex c1 i

def otherVertex {c1 : Bool} : (s : Scope c1) → Fin (otherSize s) → Vertex
  | .inl _, i => yVertex c1 i
  | .inr _, i => xVertex c1 i

def center {c1 : Bool} : (s : Scope c1) → Fin (ownSize s)
  | .inl i => i | .inr i => i

def center16 {c1 : Bool} (s : Scope c1) : Fin 16 := Fin.castLE (own_le s) (center s)
def centerVertex {c1 : Bool} (s : Scope c1) : Vertex := ownVertex s (center s)
def ownKind {c1 : Bool} (o : Owner) : Scope c1 → Bool | .inl _ => o.1 | .inr _ => o.2
def otherKind {c1 : Bool} (o : Owner) : Scope c1 → Bool | .inl _ => o.2 | .inr _ => o.1
def ownColor {c1 : Bool} : Scope c1 → Color | .inl _ => 0 | .inr _ => 1
def oppositeColor {c1 : Bool} : Scope c1 → Color | .inl _ => 1 | .inr _ => 0

theorem x_injective (c1 : Bool) : Function.Injective (xVertex c1) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [xVertex,Fin.val_mk] at this
  omega

theorem y_injective (c1 : Bool) : Function.Injective (yVertex c1) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [yVertex,Fin.val_mk] at this
  omega

theorem own_injective {c1 : Bool} (s : Scope c1) : Function.Injective (ownVertex s) := by
  cases s
  · exact x_injective c1
  · exact y_injective c1

theorem other_injective {c1 : Bool} (s : Scope c1) : Function.Injective (otherVertex s) := by
  cases s
  · exact y_injective c1
  · exact x_injective c1

theorem own_other_ne {c1 : Bool} (s : Scope c1) (a : Fin (ownSize s)) (b : Fin (otherSize s)) :
    ownVertex s a ≠ otherVertex s b := by
  cases s with
  | inl i =>
    intro h
    have ha := a.isLt
    have := congrArg Fin.val h
    simp only [ownVertex,otherVertex,xVertex,yVertex,Fin.val_mk] at this
    change a.val < firstSize c1 at ha
    omega
  | inr i =>
    intro h
    have hb := b.isLt
    have := congrArg Fin.val h
    simp only [ownVertex,otherVertex,xVertex,yVertex,Fin.val_mk] at this
    change b.val < firstSize c1 at hb
    omega

theorem own_template {c1 : Bool} {c : Host} {o : Owner} (h : Normalized c1 c o)
    (s : Scope c1) (a b : Fin (ownSize s)) (hab : a ≠ b) :
    c (ownVertex s a) (ownVertex s b) = palette (foreign (ownColor s)
      (R4333.k16Template (ownKind o s) (Fin.castLE (own_le s) a) (Fin.castLE (own_le s) b))) := by
  cases s
  · exact h.left_template a b hab
  · exact h.right_template a b hab

theorem other_template {c1 : Bool} {c : Host} {o : Owner} (h : Normalized c1 c o)
    (s : Scope c1) (a b : Fin (otherSize s)) (hab : a ≠ b) :
    c (otherVertex s a) (otherVertex s b) = palette (foreign (oppositeColor s)
      (R4333.k16Template (otherKind o s) (Fin.castLE (other_le s) a) (Fin.castLE (other_le s) b))) := by
  cases s
  · exact h.right_template a b hab
  · exact h.left_template a b hab

theorem named_high (c : Host) (h : NamedCaps c) (v : Vertex) (q : Color) (hq : q.val < 2) :
    15 ≤ colorDegree c (palette q) v := by
  have hs := named_caps_vectors c h v
  have cases : q = 0 ∨ q = 1 := by
    have : q.val = 0 ∨ q.val = 1 := by omega
    rcases this with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases cases with rfl | rfl <;> rcases hs with h | h | h | h <;> omega

/-- Exactly the scopes whose literal internal anchor remains a pentagon.
A15-cell loses five such anchors; the16-cell retains all sixteen. -/
def AnchorReady {c1 : Bool} (o : Owner) (s : Scope c1) : Prop :=
  ∀ a : Fin 5, (anchor (ownKind o s) (center16 s) a).val < ownSize s

instance {c1 : Bool} (o : Owner) (s : Scope c1) : Decidable (AnchorReady o s) :=
  inferInstanceAs (Decidable (∀ a : Fin 5, _))

def anchorIndex {c1 : Bool} {o : Owner} {s : Scope c1} (h : AnchorReady o s) (a : Fin 5) : Fin (ownSize s) :=
  ⟨(anchor (ownKind o s) (center16 s) a).val,h a⟩

def geometry {c1 : Bool} (o : Owner) (s : Scope c1) (h : AnchorReady o s)
    (roles : Fin (otherSize s) → Fin 11 → Nat) (states : Fin 6 → Nat) :
    BalancedEncoding.Geometry (otherSize s) where
  center := centerVertex s
  member := otherVertex s
  anchor := fun a => ownVertex s (anchorIndex h a)
  scopeColor := oppositeColor s
  memberColor := fun a b => R4333.k16Template (otherKind o s)
    (Fin.castLE (other_le s) a) (Fin.castLE (other_le s) b)
  roleAtom := roles
  stateAtom := states
  center_ne := fun m => own_other_ne s _ m
  anchor_ne := fun a m => own_other_ne s _ m

end UniformK60.BalancedHost

namespace UniformK60.BalancedHost

def scopes (c1 : Bool) : List (Scope c1) :=
  (List.finRange (UniformK60.HostNormalization.firstSize c1)).map Sum.inl ++
  (List.finRange 16).map Sum.inr

def embeddingScopes (c1 : Bool) (o : Owner) : List (Scope c1) :=
  (scopes c1).filter fun s => AnchorReady o s

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem scope_census : ∀ o : Owner,
    (scopes false).length = 31 ∧ (embeddingScopes false o).length = 26 ∧
    (scopes true).length = 32 ∧ (embeddingScopes true o).length = 32 := by
  decide +kernel

end UniformK60.BalancedHost
