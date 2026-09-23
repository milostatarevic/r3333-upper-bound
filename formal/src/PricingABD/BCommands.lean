import PricingABD.BPrimary
import PricingIntegration.ThresholdCompile

namespace PricingABD.BCommands
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open PricingABD.BPhysicalBounds PricingABD.BPrimary
open PricingIntegration.FoldedThreshold PricingIntegration.ThresholdCompile

structure Bound where
  xs : List Lit
  limit : Nat
  upper : Bool := false
  gate : Option Nat := none
  deriving DecidableEq
inductive Kind where
  | freeInterval (u : Fin 5) (q : Fin 4) (upper : Bool)
  | freePair (u : Fin 5) (q : Fin 3)
  | tailNonzero (u : Fin 47) (q : Fin 3)
  | tailZero (u : Fin 47)
  | cap (u : Fin 52) (q : Fin 4)
  | proxy (u : Fin 52)
  | highTotal
  deriving DecidableEq
 def nonzero (q : Fin 3) : Fin 4 := ⟨q.val+1,by omega⟩
 theorem nonzero_ne (q : Fin 3) : nonzero q≠0 := by intro h;have := congrArg Fin.val h;dsimp [nonzero]at this;omega
 def command : Kind → Bound
  | .freeInterval u q upper =>
    ⟨row tailLabels (freeLabel u) q,if upper then (if q=0 then 15 else 14) else (if q=0 then 11 else 7),upper,none⟩
  | .freePair u q => ⟨row tailLabels (freeLabel u) 0 ++ row tailLabels (freeLabel u) (nonzero q),22,false,none⟩
  | .tailNonzero u q => ⟨row tailLabels (tailLabel u) (nonzero q),if nonzero q=owner (tailLabel u) then 6 else 7,false,none⟩
  | .tailZero u => ⟨row allLabels (tailLabel u) 0,4,false,none⟩
  | .cap u q => ⟨row allLabels u q,if q=owner u then 15 else 16,true,none⟩
  | .proxy u => ⟨row tailLabels u (owner u),if owner u=0 then 14 else 9,false,some (high u)⟩
  | .highTotal => ⟨allLabels.map (fun u => (true,high u)),39,false,none⟩

 def allKinds : List Kind :=
   (List.finRange 5).flatMap (fun u => (List.finRange 4).flatMap (fun q => [.freeInterval u q false,.freeInterval u q true])) ++
   (List.finRange 5).flatMap (fun u => (List.finRange 3).map (fun q => .freePair u q)) ++
   (List.finRange 47).flatMap (fun u => (List.finRange 3).map (fun q => .tailNonzero u q)) ++
   (List.finRange 47).map Kind.tailZero ++
   (List.finRange 52).flatMap (fun u => (List.finRange 4).map (fun q => .cap u q)) ++
   (List.finRange 52).map Kind.proxy ++ [.highTotal]
 def allCommands : List Bound := allKinds.map command
 theorem allCommands_length : allCommands.length=504 := by decide +kernel

 theorem physical_command {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) (k : Kind) :
    boundHolds (primary f) (command k).xs (command k).limit (command k).upper (command k).gate := by
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
    change 22≤count (primary f) (row tailLabels (freeLabel u) 0)+count (primary f) (row tailLabels (freeLabel u) (nonzero q))
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
    by_cases hu : u.val<5
    · let i : Fin 5 := ⟨u.val,hu⟩
      have he : u=freeLabel i := rfl
      rw [he,owner_free,if_pos rfl]
      exact high_free_proxy f hc i (he ▸ hh)
    · let i : Fin 47 := ⟨u.val-5,by omega⟩
      have he : u=tailLabel i := by apply Fin.ext;dsimp [i,tailLabel];omega
      rw [he,if_neg (owner_tail_nonzero i)]
      exact high_tail_proxy f hc i (he ▸ hh)
  | highTotal =>
    simp only [command,boundHolds,Bool.false_eq_true,if_false]
    intro _
    rw [high_count]
    exact surviving_high_count f

 theorem all_physical_commands {c : Host} (f : Frame c) (hc : NoMonochromaticTriangle c) :
    ∀ b∈allCommands,boundHolds (primary f) b.xs b.limit b.upper b.gate := by
  intro b hb
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hb
  exact physical_command f hc k

#print axioms all_physical_commands
end PricingABD.BCommands
