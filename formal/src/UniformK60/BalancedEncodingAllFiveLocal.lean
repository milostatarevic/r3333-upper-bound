import UniformK60.BalancedEncodingAllFive
import UniformK60.BalancedHostAllFive

set_option autoImplicit false
namespace UniformK60.BalancedEncodingAllFive
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding
open UniformK61.BalancedEncoding (sat_map sat_flatMap)

theorem minor_full : ∀ s : Scope, guardMinor (scope s)=false := by decide

theorem actual_guard_witness {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized true c o)
    (hall : AllOwnSixteen c) (s : Scope) :
    ∃ w : GuardWitness c (guardGeometry o s),
      (BalancedAnchor.pattern false (guardKind o s) w.chosen).card=5 := by
  have hdegree := hall (centerVertex (scope s)) (ownColor (scope s))
    (by cases scope s <;> simp only [ownColor] <;> decide)
  have hcard := guard_card_five hc hn (scope s) hdegree
  obtain ⟨i,hi⟩ := BalancedAnchor.c5_complete false (otherKind o (scope s)) (castSet c (scope s))
    hcard (guard_independent hc hn (scope s)) (fun _ _ => Or.inl rfl)
  refine ⟨⟨i,?_⟩,?_⟩
  · intro m
    change c (centerVertex (scope s)) (otherVertex (scope s) m)=palette (ownColor (scope s)) ↔
      m∈Finset.univ.filter (fun v =>
        Fin.castLE (other_le (scope s)) v∈BalancedAnchor.pattern false (guardKind o s) i)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hi,cast_mem]
    simp only [guardSet,Finset.mem_filter,Finset.mem_univ,true_and]
  · rw [hi]
    exact hcard

theorem forbidFour_sat {c : Host} {o : Owner} (v : Valuation)
    (w : ∀ s : Scope,GuardWitness c (guardGeometry o s))
    (hfive : ∀ s,(BalancedAnchor.pattern false (guardKind o s) (w s).chosen).card=5)
    (hselectors : ∀ s i,v ((guardGeometry o s).selector i)=decide (i=(w s).chosen)) :
    FormulaSat v (forbidFour o) := by
  apply sat_flatMap
  intro s _
  apply sat_map
  intro i hi
  have hfour := of_decide_eq_true (List.mem_filter.mp hi).2
  have hne : i≠(w s).chosen := by
    intro he
    rw [he,hfive] at hfour
    omega
  refine ⟨negative (guardStart o s+i.val+1),by simp,?_⟩
  change v ((guardGeometry o s).selector i)=false
  have hne' : (i : Fin (guardCount o s)) ≠ (w s).chosen := hne
  exact (hselectors s i).trans (decide_eq_false hne')

#print axioms actual_guard_witness
#print axioms forbidFour_sat
end UniformK60.BalancedEncodingAllFive
