import R4333Lean.ColoringAddRoot
import R4333Lean.ProfileDFourRowCNF

/-!
# Root safety and the exact degree-fifteen cap for profile D

The semantic profile-D four-row object remembers the four root-neighbourhood
classes from which its vertices came: the four free vertices have root colour
zero, while the three tail blocks have root colours one, two, and three.
The fixed internal templates omit their own root colour, and the free block
records the corresponding prohibition explicitly.  Hence the omitted root
can be added back without creating a monochromatic triangle.

This file transports that fact all the way to the authoritative `Fin 50`
colouring used by `ProfileDFourRowCNF`.  The generic root-extension theorem
then proves, inside Lean, that every vertex has degree at most fifteen in its
own root colour.  This is a semantic strengthening only; no cardinality CNF
or unsatisfiability certificate is asserted here.
-/

namespace R4333
namespace ProfileDFourRowDegreeCap

open ColoringJoinRows
open ProfileDTripleJoinReduction
open ProfileDRowExtension
open ProfileDFourRowBoundary
open ProfileDFourRowCNF
open SingleRootStarWitness61

set_option maxRecDepth 1000000

abbrev JoinedVertex := Sum FourVertex TailVertex

/-- Root colour of a vertex in the three-block tail. -/
def tailRootColor (x : TailVertex) : Fin 4 :=
  if x.val < 15 then 1 else if x.val < 30 then 2 else 3

/-- Root colour on the semantic `Fin 4 + Fin 46` join. -/
def joinedRootColor : JoinedVertex → Fin 4
  | .inl _ => 0
  | .inr x => tailRootColor x

/-- The exact semantic joined colouring underlying a four-row extension. -/
def joinedColoring {kind : Kind} (ext : FourExtension kind) :
    EdgeColoring JoinedVertex (Fin 4) :=
  ColoringJoinRows.joinColoring ext.inside ext.tail.coloring ext.rows

theorem joinedColoring_noMono {kind : Kind} (ext : FourExtension kind) :
    NoMonochromaticTriangle (joinedColoring ext) := by
  exact (noMono_joinColoring_iff
    ext.inside ext.tail.coloring ext.rows).2
      ⟨ext.insideNoMono, ext.tail.noMono,
        ext.rowsAdmissible, ext.rowsPairCompatible⟩

private theorem tail_block_zero_rootForbidden {kind : Kind}
    (ext : FourExtension kind) (x y : TailVertex)
    (hx : x.val < 15) (hy : y.val < 15) (hxy : x ≠ y) :
    ext.tail.coloring x y ≠ 1 := by
  have hval : x.val ≠ y.val := fun h ↦ hxy (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hxVertex : blockVertex 0 x.val = x := by
      apply Fin.ext
      rw [blockVertex_val 0 (by simpa [blockSize] using hx)]
      simp [blockStart]
    have hyVertex : blockVertex 0 y.val = y := by
      apply Fin.ext
      rw [blockVertex_val 0 (by simpa [blockSize] using hy)]
      simp [blockStart]
    rw [← hxVertex, ← hyVertex]
    rw [ext.tail.templateCanonical 0 x.val y.val
      (by simpa [blockSize] using hx)
      (by simpa [blockSize] using hy) hlt]
    simpa using canonicalPalette_ne_block (1 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 0) (kind.twisted 0) x.val y.val)
  · rw [ext.tail.coloring.color_symm]
    have hyVertex : blockVertex 0 y.val = y := by
      apply Fin.ext
      rw [blockVertex_val 0 (by simpa [blockSize] using hy)]
      simp [blockStart]
    have hxVertex : blockVertex 0 x.val = x := by
      apply Fin.ext
      rw [blockVertex_val 0 (by simpa [blockSize] using hx)]
      simp [blockStart]
    rw [← hyVertex, ← hxVertex]
    rw [ext.tail.templateCanonical 0 y.val x.val
      (by simpa [blockSize] using hy)
      (by simpa [blockSize] using hx) hgt]
    simpa using canonicalPalette_ne_block (1 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 0) (kind.twisted 0) y.val x.val)

private theorem tail_block_one_rootForbidden {kind : Kind}
    (ext : FourExtension kind) (x y : TailVertex)
    (hx0 : ¬x.val < 15) (hx1 : x.val < 30)
    (hy0 : ¬y.val < 15) (hy1 : y.val < 30) (hxy : x ≠ y) :
    ext.tail.coloring x y ≠ 2 := by
  let xp : Nat := x.val - 15
  let yp : Nat := y.val - 15
  have hxp : xp < blockSize 1 := by simp [xp, blockSize]; omega
  have hyp : yp < blockSize 1 := by simp [yp, blockSize]; omega
  have hval : xp ≠ yp := by
    intro h
    apply hxy
    apply Fin.ext
    simp [xp, yp] at h
    omega
  have hxVertex : blockVertex 1 xp = x := by
    apply Fin.ext
    rw [blockVertex_val 1 hxp]
    simp [blockStart, xp]
    omega
  have hyVertex : blockVertex 1 yp = y := by
    apply Fin.ext
    rw [blockVertex_val 1 hyp]
    simp [blockStart, yp]
    omega
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · rw [← hxVertex, ← hyVertex]
    rw [ext.tail.templateCanonical 1 xp yp hxp hyp hlt]
    simpa using canonicalPalette_ne_block (2 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 1) (kind.twisted 1) xp yp)
  · rw [ext.tail.coloring.color_symm, ← hyVertex, ← hxVertex]
    rw [ext.tail.templateCanonical 1 yp xp hyp hxp hgt]
    simpa using canonicalPalette_ne_block (2 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 1) (kind.twisted 1) yp xp)

private theorem tail_block_two_rootForbidden {kind : Kind}
    (ext : FourExtension kind) (x y : TailVertex)
    (hx : ¬x.val < 30) (hy : ¬y.val < 30) (hxy : x ≠ y) :
    ext.tail.coloring x y ≠ 3 := by
  let xp : Nat := x.val - 30
  let yp : Nat := y.val - 30
  have hxp : xp < blockSize 2 := by
    simp [xp, blockSize]
    omega
  have hyp : yp < blockSize 2 := by
    simp [yp, blockSize]
    omega
  have hval : xp ≠ yp := by
    intro h
    apply hxy
    apply Fin.ext
    simp [xp, yp] at h
    omega
  have hxVertex : blockVertex 2 xp = x := by
    apply Fin.ext
    rw [blockVertex_val 2 hxp]
    simp [blockStart, xp]
    omega
  have hyVertex : blockVertex 2 yp = y := by
    apply Fin.ext
    rw [blockVertex_val 2 hyp]
    simp [blockStart, yp]
    omega
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · rw [← hxVertex, ← hyVertex]
    rw [ext.tail.templateCanonical 2 xp yp hxp hyp hlt]
    simpa using canonicalPalette_ne_block (3 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 2) (kind.twisted 2) xp yp)
  · rw [ext.tail.coloring.color_symm, ← hyVertex, ← hxVertex]
    rw [ext.tail.templateCanonical 2 yp xp hyp hxp hgt]
    simpa using canonicalPalette_ne_block (3 : Fin 4)
      (SingleRootStarCNF.templateColor
        (blockSize 2) (kind.twisted 2) yp xp)

@[simp] theorem tailRootColor_ne_zero (x : TailVertex) :
    tailRootColor x ≠ 0 := by
  by_cases hx0 : x.val < 15
  · simp [tailRootColor, hx0]
  · by_cases hx1 : x.val < 30
    · simp [tailRootColor, hx0, hx1]
    · simp [tailRootColor, hx0, hx1]

/-- Distinct vertices in one tail root class never have their root colour on
their internal edge. -/
theorem tail_rootForbidden {kind : Kind} (ext : FourExtension kind)
    (x y : TailVertex) (hxy : x ≠ y)
    (hsame : tailRootColor x = tailRootColor y) :
    ext.tail.coloring x y ≠ tailRootColor x := by
  by_cases hx0 : x.val < 15
  · have hxroot : tailRootColor x = 1 := by simp [tailRootColor, hx0]
    have hyroot : tailRootColor y = 1 := hsame.symm.trans hxroot
    have hy0 : y.val < 15 := by
      by_contra hy0
      by_cases hy1 : y.val < 30
      · simp [tailRootColor, hy0, hy1] at hyroot
      · simp [tailRootColor, hy0, hy1] at hyroot
    simpa [tailRootColor, hx0] using
      tail_block_zero_rootForbidden ext x y hx0 hy0 hxy
  · by_cases hx1 : x.val < 30
    · have hxroot : tailRootColor x = 2 := by
        simp [tailRootColor, hx0, hx1]
      have hyroot : tailRootColor y = 2 := hsame.symm.trans hxroot
      have hy0 : ¬y.val < 15 := by
        intro hy0
        simp [tailRootColor, hy0] at hyroot
      have hy1 : y.val < 30 := by
        by_contra hy1
        simp [tailRootColor, hy0, hy1] at hyroot
      simpa [tailRootColor, hx0, hx1] using
        tail_block_one_rootForbidden ext x y hx0 hx1 hy0 hy1 hxy
    · have hxroot : tailRootColor x = 3 := by
        simp [tailRootColor, hx0, hx1]
      have hyroot : tailRootColor y = 3 := hsame.symm.trans hxroot
      have hy1 : ¬y.val < 30 := by
        intro hy1
        by_cases hy0 : y.val < 15
        · simp [tailRootColor, hy0] at hyroot
        · simp [tailRootColor, hy0, hy1] at hyroot
      simpa [tailRootColor, hx0, hx1] using
        tail_block_two_rootForbidden ext x y hx1 hy1 hxy

/-- Exact root-safety condition on the semantic four-row join. -/
theorem joinedColoring_rootForbidden {kind : Kind}
    (ext : FourExtension kind) (u v : JoinedVertex) (huv : u ≠ v)
    (hsame : joinedRootColor u = joinedRootColor v) :
    joinedColoring ext u v ≠ joinedRootColor u := by
  cases u with
  | inl a =>
      cases v with
      | inl b =>
          exact ext.insideRootForbidden a b
            (fun h ↦ huv (congrArg Sum.inl h))
      | inr y =>
          exfalso
          exact tailRootColor_ne_zero y hsame.symm
  | inr x =>
      cases v with
      | inl b =>
          exfalso
          exact tailRootColor_ne_zero x hsame
      | inr y =>
          exact tail_rootForbidden ext x y
            (fun h ↦ huv (congrArg Sum.inr h)) hsame

/-- Root colour in the authoritative `Fin 50` vertex order. -/
def totalRootColor (v : ProfileDFourRowCNF.TotalVertex) : Fin 4 :=
  joinedRootColor (splitVertex v)

/-- Transport root safety to the exact `Fin 50` colouring consumed by the
checked-CNF bridge. -/
theorem totalColoring_rootForbidden {kind : Kind}
    (ext : FourExtension kind) (u v : ProfileDFourRowCNF.TotalVertex)
    (huv : u ≠ v) (hsame : totalRootColor u = totalRootColor v) :
    totalColoring ext u v ≠ totalRootColor u := by
  apply joinedColoring_rootForbidden ext (splitVertex u) (splitVertex v)
  · exact fun h ↦ huv (splitVertex_injective h)
  · exact hsame

/-- Every vertex of the authoritative profile-D `Fin 50` object has at most
fifteen neighbours in its own omitted-root colour. -/
theorem totalColoring_ownRootColorDegree_le_fifteen {kind : Kind}
    (ext : FourExtension kind) (v : ProfileDFourRowCNF.TotalVertex) :
    colorDegree (totalColoring ext) (totalRootColor v) v ≤ 15 := by
  exact colorDegree_rootColor_le_fifteen
    (totalColoring ext) totalRootColor (totalColoring_noMono ext)
    (totalColoring_rootForbidden ext) v

/-- Every displayed colour degree in the authoritative `Fin 50` object is
at most sixteen. -/
theorem colorDegree_le_sixteen {kind : Kind} (ext : FourExtension kind)
    (q : Fin 4) (v : ProfileDFourRowCNF.TotalVertex) :
    colorDegree (totalColoring ext) q v ≤ 16 := by
  fin_cases q
  · exact R4333.colorDegree_le_sixteen_of_four (totalColoring ext)
      (totalColoring_noMono ext) 0 1 2 3
        (by intro z; fin_cases z <;> simp) v
  · exact R4333.colorDegree_le_sixteen_of_four (totalColoring ext)
      (totalColoring_noMono ext) 1 0 2 3
        (by intro z; fin_cases z <;> simp) v
  · exact R4333.colorDegree_le_sixteen_of_four (totalColoring ext)
      (totalColoring_noMono ext) 2 0 1 3
        (by intro z; fin_cases z <;> simp) v
  · exact R4333.colorDegree_le_sixteen_of_four (totalColoring ext)
      (totalColoring_noMono ext) 3 0 1 2
        (by intro z; fin_cases z <;> simp) v

#print axioms R4333.ProfileDFourRowDegreeCap.tail_rootForbidden
#print axioms R4333.ProfileDFourRowDegreeCap.joinedColoring_rootForbidden
#print axioms R4333.ProfileDFourRowDegreeCap.totalColoring_rootForbidden
#print axioms R4333.ProfileDFourRowDegreeCap.totalColoring_ownRootColorDegree_le_fifteen
#print axioms R4333.ProfileDFourRowDegreeCap.colorDegree_le_sixteen

end ProfileDFourRowDegreeCap
end R4333
