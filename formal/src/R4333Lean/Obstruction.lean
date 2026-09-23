import R4333Lean.JoinC5

/-!
# From small Ramsey obstructions to four-colour upper bounds

This file contains the abstract bridge needed by the proposed order-nine and
order-ten family theorems.  It also proves the monotonicity statement showing
that a Lean proof at 61 automatically supplies the existing theorem at 62.
-/

namespace R4333

/-- Pull an edge-colouring back along a map of vertex types. -/
def pullbackColoring {V W C : Type*} (c : EdgeColoring V C) (f : W → V) :
    EdgeColoring W C where
  color u v := c (f u) (f v)
  color_symm u v := c.color_symm (f u) (f v)

/-- An injective pullback of a triangle-free colouring remains triangle-free. -/
theorem noMono_pullback {V W C : Type*} (c : EdgeColoring V C) (f : W → V)
    (hf : Function.Injective f) (hc : NoMonochromaticTriangle c) :
    NoMonochromaticTriangle (pullbackColoring c f) := by
  intro x y z hxyz hhom
  apply hc (f x) (f y) (f z)
  · exact ⟨fun h ↦ hxyz.1 (hf h), fun h ↦ hxyz.2.1 (hf h),
      fun h ↦ hxyz.2.2 (hf h)⟩
  · exact hhom

/-- Restrict a construction to fewer vertices. -/
theorem hasFourColoring_downward {m n : ℕ} (hmn : m ≤ n) :
    HasFourColoring n → HasFourColoring m := by
  rintro ⟨c, hc⟩
  exact ⟨pullbackColoring c (Fin.castLE hmn),
    noMono_pullback c (Fin.castLE hmn) (Fin.castLE_injective hmn) hc⟩

/-- Upper bounds are monotone: a proof at `m` proves every larger order. -/
theorem noFourColoring_upward {m n : ℕ} (hmn : m ≤ n)
    (hm : ¬HasFourColoring m) : ¬HasFourColoring n :=
  fun hn ↦ hm (hasFourColoring_downward hmn hn)

/-- In particular, a verified improvement to 61 automatically verifies the
currently known numerical theorem at 62. -/
theorem noFourColoring_61_implies_62 (h : ¬HasFourColoring 61) :
    ¬HasFourColoring 62 :=
  noFourColoring_upward (by omega) h

/-- A graph `g` arrows `(3,3)` when every binary colouring of its edges has a
monochromatic triangle whose three edges belong to `g`. -/
def Arrows33 {W : Type*} (g : W → W → Prop) : Prop :=
  ∀ c : EdgeColoring W Bool, ¬NoMonochromaticTriangleOn g c

/-- An injective (not necessarily induced) copy of `g` in one side of a
binary projection. -/
structure PartEmbedding {W V : Type*} (g : W → W → Prop)
    (a : EdgeColoring V Bool) (q : Bool) where
  toFun : W → V
  injective : Function.Injective toFun
  mapsEdge : ∀ {u v}, g u v → a (toFun u) (toFun v) = q

/-- An arrowing subgraph is an exact obstruction to Property B on that side
of a binary projection. -/
theorem partEmbedding_forbids_nonarrowing {W V : Type*}
    {g : W → W → Prop} {a : EdgeColoring V Bool} {q : Bool}
    (hg : Arrows33 g) (e : PartEmbedding g a q) :
  ¬ProjectionPartNonarrowing a q := by
  rintro ⟨b, hb⟩
  apply hg (pullbackColoring b e.toFun)
  intro x y z hxyz hxy hxz hyz
  apply hb (e.toFun x) (e.toFun y) (e.toFun z)
  · exact ⟨fun h ↦ hxyz.1 (e.injective h),
      fun h ↦ hxyz.2.1 (e.injective h),
      fun h ↦ hxyz.2.2 (e.injective h)⟩
  · exact ⟨e.mapsEdge hxy, e.mapsEdge hxz, e.mapsEdge hyz⟩

/-- The compiled ordinary proof of the first non-complete obstruction. -/
theorem joinC5_arrows33 : Arrows33 JoinC5Edge :=
  joinC5_arrows

/-- Abstract endpoint for a small-obstruction family theorem.  Once every
binary projection has an arrowing obstruction on at least one side, no
four-colour construction exists. -/
theorem noFourColoring_of_projection_obstructions (n : ℕ)
    (h : ∀ a : EdgeColoring (Fin n) Bool,
      ¬ProjectionPartNonarrowing a false ∨
      ¬ProjectionPartNonarrowing a true) :
    ¬HasFourColoring n := by
  intro hn
  obtain ⟨a, ha⟩ := (hasFourColoring_iff_exists_admissible_projection n).1 hn
  have hparts := (admits_refinement_iff_both_parts_nonarrowing a).1 ha
  exact (h a).elim (· hparts.1) (· hparts.2)

end R4333

#print axioms R4333.noMono_pullback
#print axioms R4333.noFourColoring_61_implies_62
#print axioms R4333.partEmbedding_forbids_nonarrowing
#print axioms R4333.noFourColoring_of_projection_obstructions
