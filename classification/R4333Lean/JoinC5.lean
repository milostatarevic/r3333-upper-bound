import R4333Lean.Basic

/-!
# A small theoretical obstruction for binary projections

This file gives an ordinary Lean proof that the graph `K3 ∨ C5` arrows
`(3,3)`: every red/blue colouring of its edges has a monochromatic triangle.
The proof is the standard odd-cycle argument, not a finite catalogue or an
untrusted computation.
-/

namespace R4333

set_option maxHeartbeats 500000

/-- The successor operation on the five vertices of a cycle. -/
def cycleNext (i : Fin 5) : Fin 5 := ⟨(i.val + 1) % 5, by omega⟩

/-- The core of the `K3 ∨ C5` proof.  If two edges of the core triangle
have colour `r` and the third has colour `!r`, avoiding monochromatic
triangles would cover an odd cycle by two independent sets. -/
theorem core_join_cycle_impossible {V : Type*} (c : EdgeColoring V Bool)
    (a b d : V) (x : Fin 5 → V) (r : Bool)
    (hab : c a b = r) (had : c a d = r) (hbd : c b d = !r)
    (habx : ∀ i, ¬HomogeneousTriangle c a b (x i))
    (hadx : ∀ i, ¬HomogeneousTriangle c a d (x i))
    (hbdx : ∀ i, ¬HomogeneousTriangle c b d (x i))
    (hacycle : ∀ i, ¬HomogeneousTriangle c a (x i) (x (cycleNext i)))
    (hbcycle : ∀ i, ¬HomogeneousTriangle c b (x i) (x (cycleNext i)))
    (hdcycle : ∀ i, ¬HomogeneousTriangle c d (x i) (x (cycleNext i))) : False := by
  have eq_not_of_ne (p q : Bool) (h : p ≠ q) : p = !q := by
    cases p <;> cases q <;> simp_all
  have eq_of_ne_not (p q : Bool) (h : p ≠ !q) : p = q := by
    cases p <;> cases q <;> simp_all
  have hax (i : Fin 5) : c a (x i) = !r := by
    apply eq_not_of_ne
    intro hair
    have hbir : c b (x i) ≠ r := by
      intro hbir
      exact habx i ⟨hab.trans hair.symm, hair.trans hbir.symm⟩
    have hdir : c d (x i) ≠ r := by
      intro hdir
      exact hadx i ⟨had.trans hair.symm, hair.trans hdir.symm⟩
    have hbi := eq_not_of_ne (c b (x i)) r hbir
    have hdi := eq_not_of_ne (c d (x i)) r hdir
    exact hbdx i ⟨hbd.trans hbi.symm, hbi.trans hdi.symm⟩
  have hcycle (i : Fin 5) : c (x i) (x (cycleNext i)) = r := by
    apply eq_of_ne_not
    intro he
    exact hacycle i
      ⟨(hax i).trans (hax (cycleNext i)).symm,
        (hax (cycleNext i)).trans he.symm⟩
  have hcover (i : Fin 5) : c b (x i) = r ∨ c d (x i) = r := by
    by_cases hb : c b (x i) = r
    · exact Or.inl hb
    · right
      by_contra hd
      have hbi := eq_not_of_ne (c b (x i)) r hb
      have hdi := eq_not_of_ne (c d (x i)) r hd
      exact hbdx i ⟨hbd.trans hbi.symm, hbi.trans hdi.symm⟩
  have hbindependent (i : Fin 5) :
      ¬(c b (x i) = r ∧ c b (x (cycleNext i)) = r) := by
    rintro ⟨hi, hj⟩
    exact hbcycle i ⟨hi.trans hj.symm, hj.trans (hcycle i).symm⟩
  have hdindependent (i : Fin 5) :
      ¬(c d (x i) = r ∧ c d (x (cycleNext i)) = r) := by
    rintro ⟨hi, hj⟩
    exact hdcycle i ⟨hi.trans hj.symm, hj.trans (hcycle i).symm⟩
  have hc0 := hcover (0 : Fin 5)
  have hc1 := hcover (1 : Fin 5)
  have hc2 := hcover (2 : Fin 5)
  have hc3 := hcover (3 : Fin 5)
  have hc4 := hcover (4 : Fin 5)
  have hb0 := hbindependent (0 : Fin 5)
  have hb1 := hbindependent (1 : Fin 5)
  have hb2 := hbindependent (2 : Fin 5)
  have hb3 := hbindependent (3 : Fin 5)
  have hb4 := hbindependent (4 : Fin 5)
  have hd0 := hdindependent (0 : Fin 5)
  have hd1 := hdindependent (1 : Fin 5)
  have hd2 := hdindependent (2 : Fin 5)
  have hd3 := hdindependent (3 : Fin 5)
  have hd4 := hdindependent (4 : Fin 5)
  norm_num [cycleNext] at hb0 hb1 hb2 hb3 hb4 hd0 hd1 hd2 hd3 hd4
  by_cases p0 : c b (x 0) = r
  · have np1 : c b (x 1) ≠ r := fun p1 ↦ hb0 p0 p1
    have np4 : c b (x 4) ≠ r := fun p4 ↦ hb4 p4 p0
    have q1 : c d (x 1) = r := hc1.resolve_left np1
    have q4 : c d (x 4) = r := hc4.resolve_left np4
    have nq2 : c d (x 2) ≠ r := fun q2 ↦ hd1 q1 q2
    have nq3 : c d (x 3) ≠ r := fun q3 ↦ hd3 q3 q4
    have p2 : c b (x 2) = r := hc2.resolve_right nq2
    have p3 : c b (x 3) = r := hc3.resolve_right nq3
    exact hb2 p2 p3
  · have q0 : c d (x 0) = r := hc0.resolve_left p0
    have nq1 : c d (x 1) ≠ r := fun q1 ↦ hd0 q0 q1
    have nq4 : c d (x 4) ≠ r := fun q4 ↦ hd4 q4 q0
    have p1 : c b (x 1) = r := hc1.resolve_right nq1
    have p4 : c b (x 4) = r := hc4.resolve_right nq4
    have np2 : c b (x 2) ≠ r := fun p2 ↦ hb1 p1 p2
    have np3 : c b (x 3) ≠ r := fun p3 ↦ hb3 p3 p4
    have q2 : c d (x 2) = r := hc2.resolve_left np2
    have q3 : c d (x 3) = r := hc3.resolve_left np3
    exact hd2 q2 q3

/-- Vertices `0,1,2` form the triangle and `3,...,7` form the pentagon. -/
def JoinC5Edge (u v : Fin 8) : Prop :=
  u ≠ v ∧
    (u.val < 3 ∨ v.val < 3 ∨
      (3 ≤ u.val ∧ 3 ≤ v.val ∧
        (u.val + 1 = v.val ∨ v.val + 1 = u.val ∨
          (u.val = 3 ∧ v.val = 7) ∨ (u.val = 7 ∧ v.val = 3))))

/-- A binary edge-colouring has no monochromatic triangle on a graph. -/
def NoMonochromaticTriangleOn {V : Type*} (g : V → V → Prop)
    (c : EdgeColoring V Bool) : Prop :=
  ∀ u v w, PairwiseDistinct u v w → g u v → g u w → g v w →
    ¬HomogeneousTriangle c u v w

/-- The graph `K3 ∨ C5` arrows `(3,3)`. -/
theorem joinC5_arrows (c : EdgeColoring (Fin 8) Bool) :
    ¬NoMonochromaticTriangleOn JoinC5Edge c := by
  intro h
  let x : Fin 5 → Fin 8 := fun i ↦ ⟨i.val + 3, by omega⟩
  have noHom (u v w : Fin 8) (hd : PairwiseDistinct u v w)
      (huv : JoinC5Edge u v) (huw : JoinC5Edge u w)
      (hvw : JoinC5Edge v w) : ¬HomogeneousTriangle c u v w :=
    h u v w hd huv huw hvw
  have hcore : ¬HomogeneousTriangle c 0 1 2 := by
    apply noHom 0 1 2
    · simp [PairwiseDistinct]
    · simp [JoinC5Edge]
    · simp [JoinC5Edge]
    · simp [JoinC5Edge]
  have hpattern :
      (∃ r, c 0 1 = r ∧ c 0 2 = r ∧ c 1 2 = !r) ∨
      (∃ r, c 1 0 = r ∧ c 1 2 = r ∧ c 0 2 = !r) ∨
      (∃ r, c 2 0 = r ∧ c 2 1 = r ∧ c 0 1 = !r) := by
    rw [HomogeneousTriangle] at hcore
    cases h01 : c 0 1 <;> cases h02 : c 0 2 <;> cases h12 : c 1 2 <;>
      simp_all [c.color_symm]
  have habx (a b : Fin 8) (ha : a.val < 3) (hb : b.val < 3)
      (hne : a ≠ b) (i : Fin 5) :
      ¬HomogeneousTriangle c a b (x i) := by
    apply noHom a b (x i)
    · refine ⟨hne, ?_, ?_⟩
      · intro heq
        have hv := congrArg Fin.val heq
        simp [x] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [x] at hv
        omega
    · exact ⟨hne, Or.inl ha⟩
    · refine ⟨?_, Or.inl ha⟩
      intro heq
      have hv := congrArg Fin.val heq
      simp [x] at hv
      omega
    · refine ⟨?_, Or.inl hb⟩
      intro heq
      have hv := congrArg Fin.val heq
      simp [x] at hv
      omega
  have hcorex (a b d : Fin 8) (ha : a.val < 3) (hb : b.val < 3)
      (hd : d.val < 3) (hne : b ≠ d) (i : Fin 5) :
      ¬HomogeneousTriangle c b d (x i) :=
    habx b d hb hd hne i
  have hcycle (a : Fin 8) (ha : a.val < 3) (i : Fin 5) :
      ¬HomogeneousTriangle c a (x i) (x (cycleNext i)) := by
    apply noHom a (x i) (x (cycleNext i))
    · refine ⟨?_, ?_, ?_⟩
      · intro heq
        have hv := congrArg Fin.val heq
        simp [x] at hv
        omega
      · intro heq
        have hv := congrArg Fin.val heq
        simp [x] at hv
        omega
      · fin_cases i <;> norm_num [x, cycleNext]
    · refine ⟨?_, Or.inl ha⟩
      intro heq
      have hv := congrArg Fin.val heq
      simp [x] at hv
      omega
    · refine ⟨?_, Or.inl ha⟩
      intro heq
      have hv := congrArg Fin.val heq
      simp [x] at hv
      omega
    · fin_cases i <;> norm_num [JoinC5Edge, x, cycleNext]
  rcases hpattern with ⟨r, h01, h02, h12⟩ | ⟨r, h10, h12, h02⟩ | ⟨r, h20, h21, h01⟩
  · exact core_join_cycle_impossible c 0 1 2 x r h01 h02 h12
      (habx 0 1 (by decide) (by decide) (by decide))
      (habx 0 2 (by decide) (by decide) (by decide))
      (hcorex 0 1 2 (by decide) (by decide) (by decide) (by decide))
      (hcycle 0 (by decide)) (hcycle 1 (by decide)) (hcycle 2 (by decide))
  · exact core_join_cycle_impossible c 1 0 2 x r h10 h12 h02
      (habx 1 0 (by decide) (by decide) (by decide))
      (habx 1 2 (by decide) (by decide) (by decide))
      (hcorex 1 0 2 (by decide) (by decide) (by decide) (by decide))
      (hcycle 1 (by decide)) (hcycle 0 (by decide)) (hcycle 2 (by decide))
  · exact core_join_cycle_impossible c 2 0 1 x r h20 h21 h01
      (habx 2 0 (by decide) (by decide) (by decide))
      (habx 2 1 (by decide) (by decide) (by decide))
      (hcorex 2 0 1 (by decide) (by decide) (by decide) (by decide))
      (hcycle 2 (by decide)) (hcycle 0 (by decide)) (hcycle 1 (by decide))

end R4333

#print axioms R4333.joinC5_arrows
