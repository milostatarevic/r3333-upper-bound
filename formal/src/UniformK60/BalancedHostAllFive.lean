import UniformK60.BalancedHostGuard

/-! A full own-color neighborhood forces each opposite-root support to
have five vertices. This is the necessary all-five alternative. -/
set_option autoImplicit false
namespace UniformK60.BalancedHost
open Ramsey61 Finset UniformK60.Physical UniformK60.ClassificationGeometry

/-- Only the own-color degree of this actual center is used. -/
theorem guard_card_five {c1 : Bool} {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized c1 c o) (s : Scope c1)
    (hdegree : colorDegree c (palette (ownColor s)) (centerVertex s) = 16) :
    (castSet c s).card=5 := by
  have hne : palette (oppositeColor s) ≠ palette (ownColor s) := by
    cases s <;> simp only [ownColor,oppositeColor] <;> decide
  have hi := BalancedStructure.inside_degree_bounds c hc (centerVertex s)
    (palette (ownColor s)) (palette (oppositeColor s)) hne 0 (root_mem hn.spokes s)
  rw [hdegree] at hi
  have he : BalancedStructure.inside c (centerVertex s) (palette (ownColor s))
      (palette (oppositeColor s)) 0 =
      attachingSupport c 0 (palette (ownColor s)) (centerVertex s) (palette (oppositeColor s)) := by
    unfold BalancedStructure.inside attachingSupport
    exact Finset.inter_comm _ _
  rw [he,←guard_card hn.spokes s] at hi
  omega

/-- In the all-C1 alternative both named high degrees are16 at every vertex. -/
def AllOwnSixteen (c : Host) : Prop :=
  ∀ v : Vertex, ∀ q : Color, q.val<2 → colorDegree c (palette q) v=16

theorem all_guard_patterns_five {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized true c o)
    (hall : AllOwnSixteen c) (s : Scope true) :
    ∃ i : BalancedAnchor.PatternIndex (guardMinor s) (otherKind o s),
      BalancedAnchor.pattern (guardMinor s) (otherKind o s) i=castSet c s ∧
      (BalancedAnchor.pattern (guardMinor s) (otherKind o s) i).card=5 := by
  obtain ⟨i,hi⟩ := actual_guard_pattern hc hn s
  refine ⟨i,hi,?_⟩
  rw [hi]
  apply guard_card_five hc hn s
  exact hall (centerVertex s) (ownColor s) (by cases s <;> simp only [ownColor] <;> decide)

#print axioms guard_card_five
end UniformK60.BalancedHost
