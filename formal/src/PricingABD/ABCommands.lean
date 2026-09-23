import PricingABD.ABRowCounts
import PricingABD.ABNumericBounds
import PricingIntegration.ThresholdCompile

set_option autoImplicit false
namespace PricingABD.ABCommands
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingABD.ABPhysicalBounds PricingABD.ABNumericBounds PricingABD.ABRowCounts
open PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold PricingIntegration.ThresholdCompile
structure Bound where
  xs : List Lit
  limit : Nat
  upper : Bool := false
  gate : Option Nat := none
  deriving DecidableEq
inductive Kind (l : Layout) where
  | freeInterval (u : Fin (freeSize l)) (q : Fin 4) (upper : Bool)
  | freePair (u : Fin (freeSize l)) (q : Fin 3)
  | tailNonzero (u : Fin (tailSize l)) (q : Fin 3)
  | tailZero (u : Fin (tailSize l))
  | cap (u : Fin (vertexCount l)) (q : Fin 4)
  | proxy (u : Fin (vertexCount l))
  | highTotal
  deriving DecidableEq
 def nonzero (q : Fin 3) : Fin 4 := ⟨q.val+1,by omega⟩
 theorem nonzero_ne (q : Fin 3) : nonzero q≠0 := by intro h;have := congrArg Fin.val h;dsimp [nonzero]at this;omega
 def command (l : Layout) : Kind l → Bound
  | .freeInterval u q upper =>
    ⟨row (tailLabels l) ((ABLayout.free l u)) q,if upper then (if q=0 then 15 else 27-lowSize l) else (if q=0 then 11 else 7),upper,none⟩
  | .freePair u q => ⟨row (tailLabels l) ((ABLayout.free l u)) 0 ++ row (tailLabels l) ((ABLayout.free l u)) (nonzero q),22,false,none⟩
  | .tailNonzero u q => ⟨row (tailLabels l) ((ABLayout.tail l u)) (nonzero q),if nonzero q=owner l (ABLayout.tail l u) then 6 else 7,false,none⟩
  | .tailZero u => ⟨row (allLabels l) ((ABLayout.tail l u)) 0,12+freeSize l-lowSize l,false,none⟩
  | .cap u q => ⟨row (allLabels l) u q,if q=owner l u then 15 else 16,true,none⟩
  | .proxy u => ⟨row (tailLabels l) u (owner l u),if owner l u=0 then 14 else 9,false,some (high l u)⟩
  | .highTotal => ⟨(allLabels l).map (fun u => (true,high l u)),tailSize l+freeSize l-lowSize l,false,none⟩

 def allKinds (l : Layout) : List (Kind l) :=
   (List.finRange (freeSize l)).flatMap (fun u => (List.finRange 4).flatMap (fun q => [.freeInterval u q false,.freeInterval u q true])) ++
   (List.finRange (freeSize l)).flatMap (fun u => (List.finRange 3).map (fun q => .freePair u q)) ++
   (List.finRange (tailSize l)).flatMap (fun u => (List.finRange 3).map (fun q => .tailNonzero u q)) ++
   (List.finRange (tailSize l)).map Kind.tailZero ++
   (List.finRange (vertexCount l)).flatMap (fun u => (List.finRange 4).map (fun q => .cap u q)) ++
   (List.finRange (vertexCount l)).map Kind.proxy ++ [.highTotal]
 def allCommands (l : Layout) : List Bound := (allKinds l).map (command l)

 theorem physical_command {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) (k : Kind l) :
    boundHolds (primary f) (command l k).xs (command l k).limit (command l k).upper (command l k).gate := by
  cases k with
  | freeInterval u q upper =>
    simp only [command,boundHolds]
    intro _
    rw [tail_row_count]
    by_cases hq : q=0
    · subst q
      have hh := free_bounds f hc u 1 (by decide)
      cases upper <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
    · have hh := free_bounds f hc u q hq
      cases upper <;> simp only [Bool.false_eq_true,if_false,if_true,hq] <;> omega
  | freePair u q =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro _
    rw [count,List.countP_append]
    change 22≤count (primary f) (row (tailLabels l) ((ABLayout.free l u)) 0)+count (primary f) (row (tailLabels l) ((ABLayout.free l u)) (nonzero q))
    rw [tail_row_count,tail_row_count]
    exact (free_bounds f hc u (nonzero q) (nonzero_ne q)).2.2.2.2
  | tailNonzero u q =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro _
    rw [tail_row_count]
    have hh := tail_nonzero_bounds f hc u (nonzero q) (nonzero_ne q)
    split_ifs with he
    · exact hh.1
    · exact hh.2 he
  | tailZero u =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro _
    rw [all_row_count]
    exact tail_zero_bound f hc u
  | cap u q =>
    simp only [command,boundHolds,if_true]
    intro _
    rw [all_row_count]
    exact retained_caps f hc u q
  | proxy u =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro hg
    have hh : f.vertex u∈Incoming c f.root := (primary_high f u).mp (hg _ (by simp))
    rw [tail_row_count]
    by_cases hu : u.val<freeSize l
    · let i : Fin (freeSize l) := ⟨u.val,hu⟩
      have he : u=ABLayout.free l i := rfl
      rw [he,ABLayout.owner_free,if_pos rfl]
      exact high_free_proxy f hc i (he ▸ hh)
    · let i : Fin (tailSize l) := ⟨u.val-freeSize l,by have hi:=u.isLt;unfold vertexCount at hi;omega⟩
      have he : u=ABLayout.tail l i := by apply Fin.ext;dsimp [i,ABLayout.tail];omega
      rw [he,if_neg ((ABLayout.owner_tail_nonzero l i))]
      exact high_tail_proxy f hc i (he ▸ hh)
  | highTotal =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro _
    rw [high_count]
    exact surviving_high_count f

 theorem all_physical_commands {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) :
    ∀ b∈allCommands l,boundHolds (primary f) b.xs b.limit b.upper b.gate := by
  intro b hb
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hb
  exact physical_command f hc k

#print axioms all_physical_commands
end PricingABD.ABCommands
