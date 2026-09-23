import R4333Lean.Obstruction

/-!
# Arithmetic core of the K61 attaching-set reduction

These lemmas isolate the certificate-independent integer arguments used by
the Fettes--Kramer--Radziszowski attaching-set route at order 61.  There are
no catalogue assumptions and no finite-search oracle in this file.
-/

namespace R4333

/-- The exact sorted colour-degree patterns at a vertex of a hypothetical
triangle-free four-colouring of `K61`, after the separate Ramsey fact has
bounded every colour degree by 16. -/
theorem degreePattern61_sorted (a b c d : ℕ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hd : d ≤ 16) (hsum : a + b + c + d = 60) :
    (a = 12 ∧ b = 16 ∧ c = 16 ∧ d = 16) ∨
    (a = 13 ∧ b = 15 ∧ c = 16 ∧ d = 16) ∨
    (a = 14 ∧ b = 14 ∧ c = 16 ∧ d = 16) ∨
    (a = 14 ∧ b = 15 ∧ c = 15 ∧ d = 16) ∨
    (a = 15 ∧ b = 15 ∧ c = 15 ∧ d = 15) := by
  omega

/-- Every such degree quadruple has at least two entries at least 15. -/
theorem degree61_two_ge_fifteen (a b c d : ℕ)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) :
    (15 ≤ a ∧ 15 ≤ b) ∨ (15 ≤ a ∧ 15 ≤ c) ∨
    (15 ≤ a ∧ 15 ≤ d) ∨ (15 ≤ b ∧ 15 ≤ c) ∨
    (15 ≤ b ∧ 15 ≤ d) ∨ (15 ≤ c ∧ 15 ≤ d) := by
  omega

/-- Every such degree quadruple has at least three entries at least 14. -/
theorem degree61_three_ge_fourteen (a b c d : ℕ)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) :
    (14 ≤ a ∧ 14 ≤ b ∧ 14 ≤ c) ∨
    (14 ≤ a ∧ 14 ≤ b ∧ 14 ≤ d) ∨
    (14 ≤ a ∧ 14 ≤ c ∧ 14 ≤ d) ∨
    (14 ≤ b ∧ 14 ≤ c ∧ 14 ≤ d) := by
  omega

/-- In particular, two distinct colours cannot both have degree at most 13
at one vertex.  This is the arithmetic input showing that the bad-pair graph
in the structural proof is triangle-free. -/
theorem degree61_two_small_impossible (a b c d : ℕ)
    (ha : a ≤ 16) (hb : b ≤ 16) (hc : c ≤ 16) (hd : d ≤ 16)
    (hsum : a + b + c + d = 60) (hab : a ≤ 13) (hbb : b ≤ 13) : False := by
  omega

/-- Two large-colour incidences per vertex on 61 vertices force one of the
four colours to be large at at least 31 vertices. -/
theorem largeIncidence_pigeonhole31 (x0 x1 x2 x3 : ℕ)
    (h : 122 ≤ x0 + x1 + x2 + x3) :
    31 ≤ x0 ∨ 31 ≤ x1 ∨ 31 ≤ x2 ∨ 31 ≤ x3 := by
  omega

/-- Arithmetic core of the seven-neighbourhood union argument.  If every
new 15-set loses at most two points to each preceding set, the seven
successive contributions are at least 15,13,11,9,7,5,3 and cannot fit in a
61-element universe. -/
theorem sevenNeighborhoods_exceed61
    (s0 s1 s2 s3 s4 s5 s6 : ℕ)
    (h0 : 15 ≤ s0) (h1 : 13 ≤ s1) (h2 : 11 ≤ s2)
    (h3 : 9 ≤ s3) (h4 : 7 ≤ s4) (h5 : 5 ≤ s5) (h6 : 3 ≤ s6) :
    63 ≤ s0 + s1 + s2 + s3 + s4 + s5 + s6 := by
  omega

/-- If the colour of `uv` has degree at least 14 at `u`, the two Ramsey
`R(3,3)=6` cross-parts of size at most five leave at least three vertices in
the cross-part leading into the selected attaching neighbourhood. -/
theorem attaching_cross_ge_three
    (edgeDegree firstCross secondCross attachingCross : ℕ)
    (hdeg : 14 ≤ edgeDegree)
    (hfirst : firstCross ≤ 5) (hsecond : secondCross ≤ 5)
    (hpartition : edgeDegree = 1 + firstCross + secondCross + attachingCross) :
    3 ≤ attachingCross := by
  omega

/-- The cross-part of size at least three and the attaching intersection are
disjoint inside a neighbourhood of size at most 16. -/
theorem attaching_order_le_thirteen
    (neighborhood attachingCross attachingOrder : ℕ)
    (hneighborhood : neighborhood ≤ 16)
    (hcross : 3 ≤ attachingCross)
    (hinside : attachingCross + attachingOrder ≤ neighborhood) :
    attachingOrder ≤ 13 := by
  omega

/-- Combined numerical endpoint of the upper attaching-set argument. -/
theorem attaching_order_range
    (edgeDegree firstCross secondCross attachingCross
      neighborhood attachingOrder : ℕ)
    (hlower : 3 ≤ attachingOrder)
    (hdeg : 14 ≤ edgeDegree)
    (hfirst : firstCross ≤ 5) (hsecond : secondCross ≤ 5)
    (hpartition : edgeDegree = 1 + firstCross + secondCross + attachingCross)
    (hneighborhood : neighborhood ≤ 16)
    (hinside : attachingCross + attachingOrder ≤ neighborhood) :
    3 ≤ attachingOrder ∧ attachingOrder ≤ 13 := by
  constructor
  · exact hlower
  · apply attaching_order_le_thirteen neighborhood attachingCross attachingOrder
      hneighborhood
    · exact attaching_cross_ge_three edgeDegree firstCross secondCross attachingCross
        hdeg hfirst hsecond hpartition
    · exact hinside

end R4333

#print axioms R4333.degreePattern61_sorted
#print axioms R4333.degree61_two_ge_fifteen
#print axioms R4333.degree61_three_ge_fourteen
#print axioms R4333.degree61_two_small_impossible
#print axioms R4333.largeIncidence_pigeonhole31
#print axioms R4333.sevenNeighborhoods_exceed61
#print axioms R4333.attaching_order_range
