import PricingIntegration.LocalRelations

namespace PricingIntegration.CoreLayout
open Ramsey61 Ramsey61.CEncodingCore PricingC
open PricingIntegration.LocalRelations

abbrev CoreBase := Fin 33 → Fin 33 → Option Color

/-- false=X-centered (omitted1, designated0), true=Y-centered
(omitted0, designated1), exactly as in both retained G producers. -/
def omittedColor (side : Bool) : Color := if side then 0 else 1
def colors (side : Bool) : Fin 3 → Color := ![if side then 1 else 0,2,3]

def paletteFn (side : Bool) (q : Fin 3) : {r : FourColor // r ≠ palette (omittedColor side)} :=
  ⟨palette (colors side q),by cases side <;> fin_cases q <;> decide⟩

private theorem paletteFn_bijective : ∀ side, Function.Bijective (paletteFn side) := by decide

noncomputable def scopePalette (side : Bool) : Fin 3 ≃ {r : FourColor // r ≠ palette (omittedColor side)} :=
  Equiv.ofBijective (paletteFn side) (paletteFn_bijective side)

structure ScopeLayout where
  side : Bool
  owner : Fin 33
  slots : Fin 10 → Fin 33
  roles : Fin 10 → Fin 16

def anchor : Fin 5 ↪ Fin 10 := ⟨Fin.castLE (by decide),Fin.castLE_injective _⟩

def spec (base : CoreBase) (l : ScopeLayout) : ScopeSpec :=
  ⟨l.roles,colors l.side,fun a b => base (l.slots a) (l.slots b)⟩

/-- This is a finite, computable layout check on literal33-vertex data.
It contains no quantification over a hypothetical host or a completion. -/
def LayoutValid (base : CoreBase) (l : ScopeLayout) : Prop :=
  Function.Injective l.slots ∧
  (∀ k, l.slots k ≠ l.owner ∧ base l.owner (l.slots k) = some (omittedColor l.side)) ∧
  (∀ j k : Fin 5, j ≠ k → ∀ q : Color,
    Allows (base (l.slots (anchor j)) (l.slots (anchor k))) q → q ≠ colors l.side 0) ∧
  (∀ j, l.roles (anchor j) = generators j) ∧
  (∀ k, (∀ j, k ≠ anchor j) → ∀ j, l.roles k ≠ generators j) ∧
  (∀ k, (∀ j, k ≠ anchor j) → ∀ j (q : Color),
    Allows (base (l.slots (anchor j)) (l.slots k)) q →
      (q = colors l.side 0 ↔ xorGraph.Adj (generators j) (l.roles k)))

instance (base : CoreBase) (l : ScopeLayout) : Decidable (LayoutValid base l) :=
  inferInstanceAs (Decidable (Function.Injective l.slots ∧
    (∀ k, l.slots k ≠ l.owner ∧ base l.owner (l.slots k) = some (omittedColor l.side)) ∧
    (∀ j k : Fin 5, j ≠ k → ∀ q : Color,
      Allows (base (l.slots (anchor j)) (l.slots (anchor k))) q → q ≠ colors l.side 0) ∧
    (∀ j, l.roles (anchor j) = generators j) ∧
    (∀ k, (∀ j, k ≠ anchor j) → ∀ j, l.roles k ≠ generators j) ∧
    (∀ k, (∀ j, k ≠ anchor j) → ∀ j (q : Color),
      Allows (base (l.slots (anchor j)) (l.slots k)) q →
        (q = colors l.side 0 ↔ xorGraph.Adj (generators j) (l.roles k)))))

def Realizes (c : Host) (phys : Fin 33 ↪ Vertex) (base : CoreBase) : Prop :=
  ∀ u v : Fin 33, u ≠ v → ∃ q : Color,
    Allows (base u v) q ∧ c (phys u) (phys v) = palette q

/-- A valid finite layout extracts its actual physical scope from one core
embedding. Scope membership, independent anchors, masks, palettes and every
known/unknown edge condition are all proved, not supplied independently. -/
noncomputable def physicalScope_of_layout
    (c : Host) (phys : Fin 33 ↪ Vertex) (base : CoreBase)
    (hcore : Realizes c phys base) (l : ScopeLayout) (hl : LayoutValid base l)
    (hhigh : 15 ≤ colorDegree c (palette (omittedColor l.side)) (phys l.owner)) :
    PhysicalScope c (spec base l) where
  owner := phys l.owner
  omitted := palette (omittedColor l.side)
  high := hhigh
  pal := scopePalette l.side
  palette_match := fun _ => rfl
  phys := (⟨l.slots,hl.1⟩ : Fin 10 ↪ Fin 33).trans phys
  mem_scope := by
    intro k
    obtain ⟨q,hq,hc⟩ := hcore l.owner (l.slots k) (hl.2.1 k).1.symm
    have he : q = omittedColor l.side := by
      simpa only [(hl.2.1 k).2,Allows] using hq
    exact (mem_colorNeighborhood c _ _ _).mpr ⟨phys.injective.ne (hl.2.1 k).1,by simpa [he] using hc⟩
  anchor := anchor
  independent := by
    intro j k hjk he
    obtain ⟨q,hq,hc⟩ := hcore (l.slots (anchor j)) (l.slots (anchor k))
      (hl.1.ne (anchor.injective.ne hjk))
    have hne := hl.2.2.1 j k hjk q hq
    apply hne
    apply palette_injective
    exact hc.symm.trans he
  anchor_roles := hl.2.2.2.1
  outside_roles := hl.2.2.2.2.1
  mask := by
    intro k hk j
    obtain ⟨q,hq,hc⟩ := hcore (l.slots (anchor j)) (l.slots k) (hl.1.ne (hk j).symm)
    have hm := hl.2.2.2.2.2 k hk j q hq
    change c (phys (l.slots (anchor j))) (phys (l.slots k)) = palette (colors l.side 0) ↔ _
    rw [hc]
    exact (show palette q = palette (colors l.side 0) ↔ q = colors l.side 0 from
      ⟨fun h => palette_injective h,fun h => congrArg palette h⟩).trans hm
  observed := by
    intro a b hab
    obtain ⟨q,hq,hc⟩ := hcore (l.slots a) (l.slots b) (hl.1.ne (Fin.ne_of_lt hab))
    change match base (l.slots a) (l.slots b) with
      | some old => c (phys (l.slots a)) (phys (l.slots b)) = palette old
      | none => c (phys (l.slots a)) (phys (l.slots b)) = palette 2 ∨
          c (phys (l.slots a)) (phys (l.slots b)) = palette 3
    cases h : base (l.slots a) (l.slots b) with
    | none =>
      simp only [h,Allows] at hq
      rcases hq with rfl | rfl
      · exact Or.inl hc
      · exact Or.inr hc
    | some old =>
      simp only [h,Allows] at hq
      exact hc.trans (congrArg palette hq)

#print axioms physicalScope_of_layout
end PricingIntegration.CoreLayout
