import UniformK60.BalancedEncodingValuation

set_option autoImplicit false
namespace UniformK60.BalancedEncoding

def linearSlot (n start : Nat) : LocalSlot n → Nat
  | .inl (m,t) => start+11*m.val+t.val+1
  | .inr k => start+11*n+k.val+1

theorem linearSlot_injective (n start : Nat) : Function.Injective (linearSlot n start) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      obtain ⟨m,t⟩ := a
      obtain ⟨p,u⟩ := b
      change start+11*m.val+t.val+1=start+11*p.val+u.val+1 at hab
      have ht := t.isLt
      have hu := u.isLt
      have hm : m=p := Fin.ext (by omega)
      have htu : t=u := Fin.ext (by omega)
      simp only [hm,htu]
    | inr k =>
      have hm := a.1.isLt
      have ht := a.2.isLt
      change start+11*a.1.val+a.2.val+1=start+11*n+k.val+1 at hab
      omega
  | inr k =>
    cases b with
    | inl b =>
      have hm := b.1.isLt
      have ht := b.2.isLt
      change start+11*n+k.val+1=start+11*b.1.val+b.2.val+1 at hab
      omega
    | inr l =>
      change start+11*n+k.val+1=start+11*n+l.val+1 at hab
      have hk : k=l := Fin.ext (by omega)
      simp only [hk]

theorem linearSlot_bounds (n start : Nat) (a : LocalSlot n) :
    start<linearSlot n start a ∧ linearSlot n start a≤start+11*n+6 := by
  cases a with
  | inl a =>
    have hm := a.1.isLt
    have ht := a.2.isLt
    simp only [linearSlot]
    constructor <;> omega
  | inr k =>
    have hk := k.isLt
    simp only [linearSlot]
    constructor <;> omega

end UniformK60.BalancedEncoding
