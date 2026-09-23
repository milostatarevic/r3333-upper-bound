/-
Copyright (c) 2026 Milos Tatarevic and contributors. All rights reserved.
Released under the MIT license in the repository root.
-/
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# Four-colour triangle Ramsey foundations

The four colours are represented by two Boolean coordinates.  This file
contains no finite computation and no imported catalogue: all results are
ordinary kernel-checked Lean theorems.
-/

namespace R4333

/-- A symmetric colouring of the unordered pairs of `V`.  Values on the
diagonal are irrelevant; all triangle predicates explicitly require three
distinct vertices. -/
@[ext]
structure EdgeColoring (V : Type*) (C : Type*) where
  color : V → V → C
  color_symm : ∀ u v, color u v = color v u

instance {V C : Type*} : CoeFun (EdgeColoring V C) (fun _ ↦ V → V → C) where
  coe c := c.color

/-- Three vertices are pairwise distinct. -/
def PairwiseDistinct {V : Type*} (x y z : V) : Prop :=
  x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- The three edges on `x,y,z` have one common colour. -/
def HomogeneousTriangle {V C : Type*} (c : EdgeColoring V C) (x y z : V) : Prop :=
  c x y = c x z ∧ c x z = c y z

/-- A complete-graph edge colouring with no monochromatic triangle. -/
def NoMonochromaticTriangle {V C : Type*} (c : EdgeColoring V C) : Prop :=
  ∀ x y z, PairwiseDistinct x y z → ¬HomogeneousTriangle c x y z

/-- Our concrete four-element colour type. -/
abbrev FourColor := Bool × Bool

/-- First binary projection of a four-colouring. -/
def firstProjection {V : Type*} (c : EdgeColoring V FourColor) : EdgeColoring V Bool where
  color u v := (c u v).1
  color_symm u v := congrArg Prod.fst (c.color_symm u v)

/-- Second binary projection of a four-colouring. -/
def secondProjection {V : Type*} (c : EdgeColoring V FourColor) : EdgeColoring V Bool where
  color u v := (c u v).2
  color_symm u v := congrArg Prod.snd (c.color_symm u v)

/-- Combine two binary colourings coordinatewise. -/
def pairColoring {V : Type*} (a b : EdgeColoring V Bool) :
    EdgeColoring V FourColor where
  color u v := (a u v, b u v)
  color_symm u v := by rw [a.color_symm, b.color_symm]

@[simp]
theorem firstProjection_pair {V : Type*} (a b : EdgeColoring V Bool) :
    firstProjection (pairColoring a b) = a := by
  ext u v
  rfl

@[simp]
theorem secondProjection_pair {V : Type*} (a b : EdgeColoring V Bool) :
    secondProjection (pairColoring a b) = b := by
  ext u v
  rfl

@[simp]
theorem pair_projections {V : Type*} (c : EdgeColoring V FourColor) :
    pairColoring (firstProjection c) (secondProjection c) = c := by
  apply EdgeColoring.ext
  funext u v
  exact Prod.eta (c u v)

/-- A triangle is homogeneous in a paired colouring exactly when it is
homogeneous in both binary projections. -/
theorem homogeneous_pair_iff {V : Type*} (a b : EdgeColoring V Bool) (x y z : V) :
    HomogeneousTriangle (pairColoring a b) x y z ↔
      HomogeneousTriangle a x y z ∧ HomogeneousTriangle b x y z := by
  simp only [HomogeneousTriangle, pairColoring, Prod.mk.injEq]
  aesop

/-- All three edges of a triangle have the specified binary value. -/
def ConstantTriangle {V : Type*} (a : EdgeColoring V Bool) (q : Bool)
    (x y z : V) : Prop :=
  a x y = q ∧ a x z = q ∧ a y z = q

theorem homogeneous_iff_exists_constant {V : Type*} (a : EdgeColoring V Bool)
    (x y z : V) :
    HomogeneousTriangle a x y z ↔ ∃ q, ConstantTriangle a q x y z := by
  constructor
  · rintro ⟨hxy, hyz⟩
    exact ⟨a x z, hxy, rfl, hyz.symm⟩
  · rintro ⟨q, hxy, hxz, hyz⟩
    exact ⟨hxy.trans hxz.symm, hxz.trans hyz.symm⟩

/-- The second bit gives a triangle-free two-colouring on the part of the
first projection whose value is `q`. -/
def FiberTriangleFree {V : Type*} (a b : EdgeColoring V Bool) (q : Bool) : Prop :=
  ∀ x y z, PairwiseDistinct x y z →
    ConstantTriangle a q x y z → ¬HomogeneousTriangle b x y z

/-- Both the graph represented by `a=true` and its complement represented by
`a=false` are triangle-free two-colourable, using `b` on their disjoint edge
sets. -/
def FiberwiseTriangleFree {V : Type*} (a b : EdgeColoring V Bool) : Prop :=
  ∀ q, FiberTriangleFree a b q

/-- Exact pointwise binary-projection equivalence. -/
theorem noMono_pair_iff_fiberwise {V : Type*} (a b : EdgeColoring V Bool) :
    NoMonochromaticTriangle (pairColoring a b) ↔ FiberwiseTriangleFree a b := by
  constructor
  · intro h q x y z hxyz ha hb
    apply h x y z hxyz
    rw [homogeneous_pair_iff]
    exact ⟨(homogeneous_iff_exists_constant a x y z).2 ⟨q, ha⟩, hb⟩
  · intro h x y z hxyz hab
    rw [homogeneous_pair_iff] at hab
    obtain ⟨q, hq⟩ := (homogeneous_iff_exists_constant a x y z).1 hab.1
    exact h q x y z hxyz hq hab.2

/-- A binary projection admits a triangle-free four-colour refinement. -/
def AdmitsFourColorRefinement {V : Type*} (a : EdgeColoring V Bool) : Prop :=
  ∃ b, NoMonochromaticTriangle (pairColoring a b)

/-- One side of a binary projection is nonarrowing for `(3,3)`. -/
def ProjectionPartNonarrowing {V : Type*} (a : EdgeColoring V Bool) (q : Bool) : Prop :=
  ∃ b, FiberTriangleFree a b q

/-- Select independently supplied two-colourings on the two edge parts. -/
def selectByProjection {V : Type*} (a bFalse bTrue : EdgeColoring V Bool) :
    EdgeColoring V Bool where
  color u v := if a u v then bTrue u v else bFalse u v
  color_symm u v := by
    rw [a.color_symm u v, bTrue.color_symm u v, bFalse.color_symm u v]

theorem fiber_select_false {V : Type*} (a bFalse bTrue : EdgeColoring V Bool)
    (h : FiberTriangleFree a bFalse false) :
    FiberTriangleFree a (selectByProjection a bFalse bTrue) false := by
  intro x y z hxyz ha
  have hxy : a x y = false := ha.1
  have hxz : a x z = false := ha.2.1
  have hyz : a y z = false := ha.2.2
  simpa [HomogeneousTriangle, selectByProjection, hxy, hxz, hyz] using
    h x y z hxyz ha

theorem fiber_select_true {V : Type*} (a bFalse bTrue : EdgeColoring V Bool)
    (h : FiberTriangleFree a bTrue true) :
    FiberTriangleFree a (selectByProjection a bFalse bTrue) true := by
  intro x y z hxyz ha
  have hxy : a x y = true := ha.1
  have hxz : a x z = true := ha.2.1
  have hyz : a y z = true := ha.2.2
  simpa [HomogeneousTriangle, selectByProjection, hxy, hxz, hyz] using
    h x y z hxyz ha

/-- The graph/complement factorisation: a projection admits a four-colour
refinement iff its edge graph and complementary edge graph are independently
nonarrowing for `(3,3)`. -/
theorem admits_refinement_iff_both_parts_nonarrowing {V : Type*}
    (a : EdgeColoring V Bool) :
    AdmitsFourColorRefinement a ↔
      ProjectionPartNonarrowing a false ∧ ProjectionPartNonarrowing a true := by
  constructor
  · rintro ⟨b, hb⟩
    have hf := (noMono_pair_iff_fiberwise a b).1 hb
    exact ⟨⟨b, hf false⟩, ⟨b, hf true⟩⟩
  · rintro ⟨⟨bFalse, hFalse⟩, ⟨bTrue, hTrue⟩⟩
    let b := selectByProjection a bFalse bTrue
    refine ⟨b, (noMono_pair_iff_fiberwise a b).2 ?_⟩
    intro q
    cases q
    · exact fiber_select_false a bFalse bTrue hFalse
    · exact fiber_select_true a bFalse bTrue hTrue

/-- Existence of a four-colouring on a fixed finite order. -/
def HasFourColoring (n : ℕ) : Prop :=
  ∃ c : EdgeColoring (Fin n) FourColor, NoMonochromaticTriangle c

/-- Existential form of the projection reduction. -/
theorem hasFourColoring_iff_exists_admissible_projection (n : ℕ) :
    HasFourColoring n ↔ ∃ a : EdgeColoring (Fin n) Bool, AdmitsFourColorRefinement a := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨firstProjection c, secondProjection c, ?_⟩
    simpa using hc
  · rintro ⟨a, b, hab⟩
    exact ⟨pairColoring a b, hab⟩

end R4333

#print axioms R4333.homogeneous_pair_iff
#print axioms R4333.noMono_pair_iff_fiberwise
#print axioms R4333.admits_refinement_iff_both_parts_nonarrowing
#print axioms R4333.hasFourColoring_iff_exists_admissible_projection
