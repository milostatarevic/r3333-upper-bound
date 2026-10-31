import UniformK60.CEntranceSourceDefs
import UniformK60.UnitTransport

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.CEntranceSource
open Ramsey61 UniformK60.Physical
open CompletionC.NativeMatrices

lemma coordinate_some (mode : Mode) (p : Fin 737) (v : Vertex)
    (a : Fin (pairTable p).shape.dimension) (h : coordinate mode p v=some a) :
    matrixVertex mode p a=v := by
  have hh : (matrixVertex mode p a==v)=true := List.find?_some (p:=fun x : Fin (pairTable p).shape.dimension => matrixVertex mode p x==v) (a:=a) h
  exact beq_iff_eq.mp hh

lemma fixedColor_matches {mode : Mode} {p : Fin 737} {j : Fin (pairTable p).count} {c : Host}
    (w : SourceWitness mode p j c) (a b : Vertex) (hab : a<b) (q : Color)
    (he : fixedColor mode p j a b=some q) : c a b=palette q := by
  have habv : a.val<b.val := hab
  unfold fixedColor at he
  split_ifs at he with h0 hl hr
  · subst a
    exact (w.spokes b (ne_of_gt hab)).trans (congrArg palette (Option.some.inj he))
  · have ha : a.val-leftStart mode<leftSize mode := by unfold rightStart at hl;omega
    have hb : b.val-leftStart mode<leftSize mode := by unfold rightStart at hl;omega
    let aa : Fin (leftSize mode) := ⟨a.val-leftStart mode,ha⟩
    let bb : Fin (leftSize mode) := ⟨b.val-leftStart mode,hb⟩
    have ea : leftVertex mode aa=a := by
      apply Fin.ext
      have he : leftStart mode+aa.val=a.val := by dsimp [aa];omega
      change (leftStart mode+aa.val)%60=a.val
      rw [he,Nat.mod_eq_of_lt a.isLt]
    have eb : leftVertex mode bb=b := by
      apply Fin.ext
      have he : leftStart mode+bb.val=b.val := by dsimp [bb];omega
      change (leftStart mode+bb.val)%60=b.val
      rw [he,Nat.mod_eq_of_lt b.isLt]
    have hn : aa≠bb := by
      intro h
      have hh := congrArg (leftVertex mode) h
      rw [ea,eb] at hh
      exact (ne_of_lt hab) hh
    have h := w.left aa bb hn
    rw [ea,eb] at h
    have hq : PricingABD.ABGeometry.foreign 1 (leftTemplate mode (leftType p) aa bb)=q := by
      simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using Option.some.inj he
    exact h.trans (congrArg palette hq)
  · have ha : a.val-rightStart mode<16 := by omega
    have hb : b.val-rightStart mode<16 := by omega
    let aa : Fin 16 := ⟨a.val-rightStart mode,ha⟩
    let bb : Fin 16 := ⟨b.val-rightStart mode,hb⟩
    have ea : rightVertex mode aa=a := by
      apply Fin.ext
      have he : rightStart mode+aa.val=a.val := by dsimp [aa];omega
      change (rightStart mode+aa.val)%60=a.val
      rw [he,Nat.mod_eq_of_lt a.isLt]
    have eb : rightVertex mode bb=b := by
      apply Fin.ext
      have he : rightStart mode+bb.val=b.val := by dsimp [bb];omega
      change (rightStart mode+bb.val)%60=b.val
      rw [he,Nat.mod_eq_of_lt b.isLt]
    have hn : aa≠bb := by
      intro h
      have hh := congrArg (rightVertex mode) h
      rw [ea,eb] at hh
      exact (ne_of_lt hab) hh
    have h := w.right aa bb hn
    rw [ea,eb] at h
    have hq : PricingABD.ABGeometry.foreign 2 (R4333.k16Template (rightType p) aa bb)=q := by
      simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using Option.some.inj he
    exact h.trans (congrArg palette hq)
  · cases hca : coordinate mode p a with
    | none => simp [hca] at he
    | some x =>
      cases hcb : coordinate mode p b with
      | none => simp [hca,hcb] at he
      | some y =>
        simp only [hca,hcb] at he
        split_ifs at he with hxy
        · have h := w.matrix x y hxy
          rw [coordinate_some mode p a x hca,coordinate_some mode p b y hcb] at h
          exact h.trans (congrArg palette (Option.some.inj he))

/-- The executable finite transport checker recognizes only facts proved by
the actual physical source witness. In particular negative units retain
their exact marked-neighborhood meaning. -/
theorem sourceFact_matches {mode : Mode} {p : Fin 737} {j : Fin (pairTable p).count} {c : Host}
    (w : SourceWitness mode p j c) (u : Core.PhysicalUnit)
    (h : sourceFact mode p j u=true) : Core.UnitMatches c u := by
  let a := min u.u u.v
  let b := max u.u u.v
  change (decide (a<b) && _)=true at h
  rw [Bool.and_eq_true_iff] at h
  obtain ⟨hab,h⟩ := h
  have hab : a<b := of_decide_eq_true hab
  have hn : u.u≠u.v := by intro he;simp [a,b,he] at hab
  have hs : c u.u u.v=c a b := by
    by_cases hl : u.u≤u.v
    · simp [a,b,min_eq_left hl,max_eq_right hl]
    · have hl' : u.v≤u.u := le_of_lt (lt_of_not_ge hl)
      simpa [a,b,min_eq_right hl',max_eq_left hl'] using c.color_symm u.u u.v
  refine ⟨hn,?_⟩
  cases hp : u.positive with
  | false =>
    simp only [hp,Bool.false_eq_true,if_false,Bool.and_eq_true_iff,beq_iff_eq,Bool.not_eq_true] at h
    obtain ⟨⟨hq,hb⟩,hm⟩ := h
    simp only [hp,Bool.false_eq_true,if_false]
    intro he
    have hh : c a 59=palette 3 := by rw [←hb,←hs];simpa only [hq] using he
    have ht : member mode p a=true := (w.membership a (by rw [←hb];exact ne_of_lt hab)).mp hh
    change (!member mode p a)=true at hm
    rw [ht] at hm
    contradiction
  | true =>
    simp only [hp,if_true,Bool.or_eq_true_iff,Bool.and_eq_true_iff,beq_iff_eq] at h
    simp only [hp,if_true]
    rcases h with h|⟨⟨hq,hb⟩,hm⟩
    · exact hs.trans (fixedColor_matches w a b hab u.q h)
    · have hh : c a 59=palette 3 := (w.membership a (by rw [←hb];exact ne_of_lt hab)).mpr hm
      exact hs.trans (by simpa only [hq,show b=59 from hb] using hh)

#print axioms sourceFact_matches
end UniformK60.CEntranceSource
