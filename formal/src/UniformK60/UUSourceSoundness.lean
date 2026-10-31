import UniformK60.UUSourceFacts
set_option autoImplicit false
namespace UniformK60.UUSourceSoundness
open Ramsey61 UniformK61.Core UniformK61.UUSupportData UniformK61.UUSourceDefs
open UniformK60.UUSourceFacts

lemma coordinate_some (p : Pair) (v : Vertex) (a : Fin (shape p).dimension)
 (h : coordinate p v=some a) : matrixVertex p a=v := by
 have hh:=coordinate_ok p v
 simpa only [CoordinateOK,h] using hh

lemma fixedColor_matches {q : Bool} {p : Pair} {i : Fin 600} {c : UnitRestriction.ReferenceColoring}
 (w : SourceFacts q p i c) (a b : Vertex) (hab : a<b) (color : Color)
 (he : fixedColor q p i a b=some color) : c a b=palette color := by
 have habv : a.val<b.val := hab
 unfold fixedColor at he
 split_ifs at he with h0 hl hr hq
 · cases h0
   have hn : b≠0 := ne_of_gt hab
   exact (w.spokes b hn).trans (congrArg palette (Option.some.inj he))
 · have ha : a.val-15<15 := by omega
   have hb : b.val-15<15 := by omega
   let aa : Fin 15:=⟨a.val-15,ha⟩
   let bb : Fin 15:=⟨b.val-15,hb⟩
   have ea : leftVertex aa=a := by apply Fin.ext;dsimp[leftVertex,aa];omega
   have eb : leftVertex bb=b := by apply Fin.ext;dsimp[leftVertex,bb];omega
   have hn : aa≠bb := by intro h;have:=congrArg leftVertex h;rw[ea,eb] at this;exact (ne_of_lt hab) this
   have h:=w.left aa bb hn
   change c (leftVertex aa) (leftVertex bb)=_ at h
   rw[ea,eb] at h
   have hc : PricingABD.ABGeometry.foreign 1 (R4333.k15Template false aa bb)=color := by
     simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using Option.some.inj he
   exact h.trans (congrArg palette hc)
 · have ha : a.val-30<15 := by have := b.isLt;omega
   have hb : b.val-30<15 := by omega
   let aa : Fin 15:=⟨a.val-30,ha⟩
   let bb : Fin 15:=⟨b.val-30,hb⟩
   have ea : rightVertex aa=a := by apply Fin.ext;dsimp[rightVertex,aa];omega
   have eb : rightVertex bb=b := by apply Fin.ext;dsimp[rightVertex,bb];omega
   have hn : aa≠bb := by intro h;have:=congrArg rightVertex h;rw[ea,eb] at this;exact (ne_of_lt hab) this
   have h:=w.right aa bb hn
   change c (rightVertex aa) (rightVertex bb)=_ at h
   rw[ea,eb] at h
   have hc : PricingABD.ABGeometry.foreign 2 (R4333.k15Template false aa bb)=color := by
     simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using Option.some.inj he
   exact h.trans (congrArg palette hc)
 · have ha : a.val-45<16 := by have := a.isLt;omega
   have hb : b.val-45<16 := by have := b.isLt;omega
   let aa : Fin 16:=⟨a.val-45,ha⟩
   let bb : Fin 16:=⟨b.val-45,hb⟩
   have ea : markedVertex aa=a := by apply Fin.ext;dsimp[markedVertex,aa];omega
   have eb : markedVertex bb=b := by apply Fin.ext;dsimp[markedVertex,bb];omega
   have hn : aa≠bb := by intro h;have:=congrArg markedVertex h;rw[ea,eb] at this;exact (ne_of_lt hab) this
   have h:=w.marked aa bb hn
   change c (markedVertex aa) (markedVertex bb)=_ at h
   rw[ea,eb] at h
   have hc : PricingABD.ABGeometry.foreign 3 (R4333.k16Template q aa bb)=color := by
     simpa only [Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using Option.some.inj he
   exact h.trans (congrArg palette hc)
 · cases hca:coordinate p a with
   | none => simp[hca] at he
   | some x =>
     cases hcb:coordinate p b with
     | none => simp[hca,hcb] at he
     | some y =>
       simp only [hca,hcb] at he
       split_ifs at he with hxy
       · have h:=w.matrix x y hxy
         rw[coordinate_some p a x hca,coordinate_some p b y hcb] at h
         exact h.trans (congrArg palette (Option.some.inj he))

/-- The executable source predicate only recognizes facts of the supplied
reference facts, including exact signed membership of its marked neighborhood. -/
theorem sourceFact_matches {q : Bool} {p : Pair} {i : Fin 600} {c : UnitRestriction.ReferenceColoring}
 (w : SourceFacts q p i c) (u : PhysicalUnit) (h : sourceFact q p i u=true) :
 UnitMatches c u := by
 let a:=min u.u u.v
 let b:=max u.u u.v
 change (decide (a<b) && _)=true at h
 rw [Bool.and_eq_true_iff] at h
 obtain ⟨hab,h⟩:=h
 have hab : a<b:=of_decide_eq_true hab
 have hn : u.u≠u.v := by intro he;simp[a,b,he] at hab
 have hs : c u.u u.v=c a b := by
   by_cases hl:u.u≤u.v
   · simp[a,b,min_eq_left hl,max_eq_right hl]
   · have hl':u.v≤u.u:=le_of_lt (lt_of_not_ge hl)
     simpa[a,b,min_eq_right hl',max_eq_left hl'] using c.color_symm u.u u.v
 refine ⟨hn,?_⟩
 cases hp:u.positive with
 | false =>
   simp only[hp,Bool.false_eq_true,if_false,Bool.and_eq_true_iff,beq_iff_eq] at h
   obtain ⟨⟨hq,hb⟩,hm⟩:=h
   simp only[Bool.false_eq_true,if_false]
   intro he
   have hh:c a 60=palette 3:=by rw[←hb,←hs];simpa only[hq] using he
   have ht:member p a=true:=(w.membership a (by rw[←hb];exact ne_of_lt hab)).mp hh
   change (!member p a)=true at hm
   rw[ht] at hm
   contradiction
 | true =>
   simp only[hp,if_true,Bool.or_eq_true_iff,Bool.and_eq_true_iff,beq_iff_eq] at h
   simp only[if_true]
   rcases h with h|⟨⟨hq,hb⟩,hm⟩
   · exact hs.trans (fixedColor_matches w a b hab u.q h)
   · have hh:c a 60=palette 3:=(w.membership a (by rw[←hb];exact ne_of_lt hab)).mpr hm
     exact hs.trans (by simpa only[hq,show b=60 from hb] using hh)

#print axioms sourceFact_matches
end UniformK60.UUSourceSoundness
