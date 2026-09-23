import PricingIntegration.FoldedThreshold

set_option autoImplicit false
namespace PricingABD.KnownPull
open Ramsey61.DenseCounter PricingIntegration.FoldedThreshold

/-- A proof-only partial inverse of an injective physical-atom numbering.
The formula and its emitted bytes use the original executable numbering. -/
noncomputable def pull {α : Type} (code : α → Nat) (source : α → Option Bool) : Known :=
  by
    classical
    exact fun a => if h : ∃x,code x=a then source h.choose else none

theorem at_code {α : Type} (code : α → Nat) (hi : Function.Injective code)
    (source : α → Option Bool) (x : α) : pull code source (code x)=source x := by
  classical
  have hx : ∃y,code y=code x := ⟨x,rfl⟩
  rw [pull,dif_pos hx]
  exact congrArg source (hi hx.choose_spec)

theorem outside {α : Type} (code : α → Nat) (source : α → Option Bool)
    (a : Nat) (h : ∀x,code x≠a) : pull code source a=none := by
  classical
  unfold pull
  exact dif_neg (by simpa only [not_exists] using h)

theorem sound {α : Type} (code : α → Nat) (source : α → Option Bool)
    (v : Valuation) (hs : ∀x b,source x=some b → v (code x)=b) : Sound v (pull code source) := by
  classical
  intro a b h
  unfold pull at h
  split_ifs at h with he
  · have hh:=hs he.choose b h
    simpa only [he.choose_spec] using hh

theorem domain {α : Type} (code : α → Nat) (hi : Function.Injective code)
    (source : α → Option Bool) (a : Nat) :
    pull code source a=none ↔ ∀x,code x=a → source x=none := by
  classical
  constructor
  · intro h x hx
    rw [←hx,at_code code hi source x] at h
    exact h
  · intro h
    unfold pull
    split_ifs with he
    · exact h he.choose he.choose_spec
    · rfl

#print axioms sound
#print axioms at_code
end PricingABD.KnownPull
