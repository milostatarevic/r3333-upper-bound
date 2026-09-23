import R4333Lean.Attaching61

/-!
# Adding one coloured root

This file abstracts the elementary semantic step used by every rooted Ramsey
decomposition.  A colouring on `V` extends to `Option V` by assigning a
prescribed root-edge colour to each old vertex.  The extension is
triangle-free exactly under the expected same-root-colour prohibition.
-/

namespace R4333

/-- Add a new root (`none`) to a coloured complete graph.  The value on the
root loop is irrelevant to triangle statements but is supplied explicitly. -/
def addRootColoring {V C : Type*} (base : EdgeColoring V C)
    (rootColor : V → C) (rootLoop : C) : EdgeColoring (Option V) C where
  color
    | none, none => rootLoop
    | none, some x => rootColor x
    | some x, none => rootColor x
    | some x, some y => base x y
  color_symm u v := by
    cases u <;> cases v <;> simp [base.color_symm]

@[simp] theorem addRootColoring_none_some {V C : Type*}
    (base : EdgeColoring V C) (rootColor : V → C) (rootLoop : C) (x : V) :
    addRootColoring base rootColor rootLoop none (some x) = rootColor x := rfl

@[simp] theorem addRootColoring_some_some {V C : Type*}
    (base : EdgeColoring V C) (rootColor : V → C) (rootLoop : C) (x y : V) :
    addRootColoring base rootColor rootLoop (some x) (some y) = base x y := rfl

/-- The precise condition under which adding the root preserves the absence
of monochromatic triangles. -/
theorem addRootColoring_noMono {V C : Type*}
    (base : EdgeColoring V C) (rootColor : V → C) (rootLoop : C)
    (hbase : NoMonochromaticTriangle base)
    (hroot : ∀ x y : V, x ≠ y → rootColor x = rootColor y →
      base x y ≠ rootColor x) :
    NoMonochromaticTriangle (addRootColoring base rootColor rootLoop) := by
  intro x y z hxyz hmono
  cases x with
  | none =>
      cases y with
      | none => exact hxyz.1 rfl
      | some y =>
          cases z with
          | none => exact hxyz.2.1 rfl
          | some z =>
              have hsame : rootColor y = rootColor z := hmono.1
              have hyz : y ≠ z := fun hyz ↦ hxyz.2.2 (congrArg some hyz)
              apply hroot y z hyz hsame
              exact hmono.2.symm.trans hmono.1.symm
  | some x =>
      cases y with
      | none =>
          cases z with
          | none => exact hxyz.2.2 rfl
          | some z =>
              have hsame : rootColor x = rootColor z :=
                hmono.1.trans hmono.2
              have hxz : x ≠ z := fun hxz ↦ hxyz.2.1 (congrArg some hxz)
              apply hroot x z hxz hsame
              exact hmono.1.symm
      | some y =>
          cases z with
          | none =>
              have hsame : rootColor x = rootColor y := hmono.2
              have hxy : x ≠ y := fun hxy ↦ hxyz.1 (congrArg some hxy)
              apply hroot x y hxy hsame
              exact hmono.1
          | some z =>
              have hxyz' : PairwiseDistinct x y z :=
                ⟨fun hxy ↦ hxyz.1 (congrArg some hxy),
                 fun hxz ↦ hxyz.2.1 (congrArg some hxz),
                 fun hyz ↦ hxyz.2.2 (congrArg some hyz)⟩
              exact hbase x y z hxyz' hmono

/-- On four colours, the displayed root edge consumes one unit of the
universal degree-sixteen cap.  Thus every old vertex has degree at most
fifteen in its own root colour inside the graph before the root is added. -/
theorem colorDegree_rootColor_le_fifteen {V : Type*}
    [Fintype V] [DecidableEq V]
    (base : EdgeColoring V (Fin 4)) (rootColor : V → Fin 4)
    (hbase : NoMonochromaticTriangle base)
    (hroot : ∀ x y : V, x ≠ y → rootColor x = rootColor y →
      base x y ≠ rootColor x)
    (x : V) :
    colorDegree base (rootColor x) x ≤ 15 := by
  let rooted := addRootColoring base rootColor 0
  have hrootedNoMono : NoMonochromaticTriangle rooted :=
    addRootColoring_noMono base rootColor 0 hbase hroot
  have hrootedCap : colorDegree rooted (rootColor x) (some x) ≤ 16 := by
    generalize hq : rootColor x = q
    fin_cases q
    · simpa [hq] using colorDegree_le_sixteen_of_four rooted hrootedNoMono
        0 1 2 3 (by intro q; fin_cases q <;> simp) (some x)
    · simpa [hq] using colorDegree_le_sixteen_of_four rooted hrootedNoMono
        1 0 2 3 (by intro q; fin_cases q <;> simp) (some x)
    · simpa [hq] using colorDegree_le_sixteen_of_four rooted hrootedNoMono
        2 0 1 3 (by intro q; fin_cases q <;> simp) (some x)
    · simpa [hq] using colorDegree_le_sixteen_of_four rooted hrootedNoMono
        3 0 1 2 (by intro q; fin_cases q <;> simp) (some x)
  let support : Finset V := colorNeighborhood base (rootColor x) x
  let lifted : Finset (Option V) := support.image some
  let withRoot : Finset (Option V) := insert none lifted
  have hcard : withRoot.card = support.card + 1 := by
    calc
      withRoot.card = lifted.card + 1 := by
        apply Finset.card_insert_of_notMem
        simp [lifted]
      _ = support.card + 1 := by
        rw [show lifted.card = support.card by
          exact Finset.card_image_of_injective support
            (Option.some_injective V)]
  have hsubset : withRoot ⊆ colorNeighborhood rooted (rootColor x) (some x) := by
    intro v hv
    simp only [withRoot, Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact (mem_colorNeighborhood rooted (rootColor x) (some x) none).2
        ⟨(Option.some_ne_none x).symm, rfl⟩
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      have hy' :=
        (mem_colorNeighborhood base (rootColor x) x y).1 hy
      exact (mem_colorNeighborhood rooted (rootColor x) (some x) (some y)).2
        ⟨fun h ↦ hy'.1 (Option.some.inj h), hy'.2⟩
  have hwithRootBound : withRoot.card ≤
      (colorNeighborhood rooted (rootColor x) (some x)).card :=
    Finset.card_le_card hsubset
  change support.card ≤ 15
  change (colorNeighborhood rooted (rootColor x) (some x)).card ≤ 16 at hrootedCap
  omega

#print axioms R4333.addRootColoring_noMono
#print axioms R4333.colorDegree_rootColor_le_fifteen

end R4333
