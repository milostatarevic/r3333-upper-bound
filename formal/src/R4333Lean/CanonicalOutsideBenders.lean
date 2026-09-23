import R4333Lean.CanonicalAttachingHost
import R4333Lean.OutsideCoreCNF

/-!
# The outside-list cut on the canonical attaching host

`CanonicalAttachingHost` gives a single six-region vertex type, while
`OutsideListBenders` states the learned-cut theorem for arbitrary disjoint
embeddings.  This file joins the two: the outside region is embedded as the
sixth summand and every other summand is exposed.

The bridge is deliberately semantic.  A later checked formula may choose
any finite core of outside pair/colour restrictions; once that core is
proved uncolourable, the corresponding outer availability clause follows
without trusting the search program that discovered it.
-/

namespace R4333

/-- The canonical vertices in the outside region. -/
abbrev CanonicalOutsideVertex (du dv k : ℕ) :=
  Fin (attachingRegionSize du dv k .outside)

/-- Every canonical vertex outside the sixth summand is exposed. -/
abbrev CanonicalExposedVertex (du dv k : ℕ) :=
  {x : CanonicalAttachingVertex du dv k // x.1 ≠ .outside}

/-- Embed the five exposed regions in the whole canonical host. -/
def canonicalExposedEmbedding (du dv k : ℕ) :
    CanonicalExposedVertex du dv k ↪ CanonicalAttachingVertex du dv k :=
  Function.Embedding.subtype _

/-- Embed the outside region in the whole canonical host. -/
def canonicalOutsideEmbedding (du dv k : ℕ) :
    CanonicalOutsideVertex du dv k ↪ CanonicalAttachingVertex du dv k where
  toFun i := ⟨.outside, i⟩
  inj' := by
    intro i j hij
    simpa using hij

@[simp] theorem canonicalOutsideEmbedding_region
    (du dv k : ℕ) (x : CanonicalOutsideVertex du dv k) :
    (canonicalOutsideEmbedding du dv k x).1 = .outside :=
  rfl

/-- The two canonical embeddings have disjoint images by construction. -/
theorem canonicalExposedOutside_disjoint (du dv k : ℕ) :
    ExposedOutsideDisjoint
      (canonicalExposedEmbedding du dv k)
      (canonicalOutsideEmbedding du dv k) := by
  intro center x heq
  apply center.property
  exact congrArg Sigma.fst heq

/-- The mixed high-overlap branch used by the discovery search exposes 20
vertices and leaves an exact outside `K₄₁`.  These are type cardinalities,
not dimensions asserted by an external encoder. -/
@[simp] theorem canonicalOutsideVertex_card_15_16_13 :
    Fintype.card (CanonicalOutsideVertex 15 16 13) = 41 := by
  decide

@[simp] theorem canonicalExposedVertex_card_15_16_13 :
    Fintype.card (CanonicalExposedVertex 15 16 13) = 20 := by
  decide

/-- The exposed-to-outside incidence table of a colouring on the canonical
attaching host. -/
def canonicalExposedIncidence
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor) :
    ExposedIncidence
      (CanonicalExposedVertex du dv k)
      (CanonicalOutsideVertex du dv k)
      FourColor :=
  coloringExposedIncidence c
    (canonicalExposedEmbedding du dv k)
    (canonicalOutsideEmbedding du dv k)

/-- Restrict a canonical-host colouring to its outside summand. -/
def canonicalOutsideColoring
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor) :
    EdgeColoring (CanonicalOutsideVertex du dv k) FourColor :=
  outsideInducedColoring c (canonicalOutsideEmbedding du dv k)

@[simp] theorem canonicalOutsideColoring_apply
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor)
    (x y : CanonicalOutsideVertex du dv k) :
    canonicalOutsideColoring c x y =
      c (canonicalOutsideEmbedding du dv k x)
        (canonicalOutsideEmbedding du dv k y) :=
  rfl

/-- A collision at any of the five exposed regions forbids that colour on
the corresponding outside edge. -/
theorem canonicalOutside_edge_ne_of_collision
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor)
    (hc : NoMonochromaticTriangle c)
    {x y : CanonicalOutsideVertex du dv k} (hxy : x ≠ y)
    {q : FourColor}
    (hcollision : ExposedIncidenceCollision
      (canonicalExposedIncidence c) x y q) :
    canonicalOutsideColoring c x y ≠ q := by
  exact outside_edge_ne_of_exposedIncidenceCollision c
    (canonicalExposedEmbedding du dv k)
    (canonicalOutsideEmbedding du dv k)
    (canonicalExposedOutside_disjoint du dv k) hc hxy hcollision

/-- The generic Benders theorem, specialized to the exact canonical
outside/exposed split used by the order-61 reduction. -/
theorem canonicalOutsideListBendersClause_of_coreUnsatisfiable
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor)
    (hc : NoMonochromaticTriangle c)
    (core : Finset
      (OutsidePairColorRestriction
        (CanonicalOutsideVertex du dv k) FourColor))
    (hcore : OutsideRestrictionCoreUnsatisfiable core) :
    OutsideListBendersClause (canonicalExposedIncidence c) core := by
  exact outsideListBendersClause_of_coreUnsatisfiable c
    (canonicalExposedEmbedding du dv k)
    (canonicalOutsideEmbedding du dv k)
    (canonicalExposedOutside_disjoint du dv k) hc core hcore

/-- End-to-end checked canonical cut.  The inner formula is Lean-defined and
its LRAT proof is checked in the kernel before the availability disjunction
is used by the outer search. -/
theorem canonicalOutsideListBendersClause_of_lrat
    {du dv k : ℕ}
    (c : EdgeColoring (CanonicalAttachingVertex du dv k) FourColor)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List
      (OutsidePairColorRestriction
        (CanonicalOutsideVertex du dv k) FourColor))
    (hunsat : (OutsideCoreCNF.outsideCoreFmla
      (attachingRegionSize du dv k .outside) 4
      OutsideCoreCNF.fourColorEquivFin4 restrictions).proof []) :
    OutsideListBendersClause (canonicalExposedIncidence c)
      restrictions.toFinset := by
  exact OutsideCoreCNF.outsideListBendersClause_of_lrat
    OutsideCoreCNF.fourColorEquivFin4 c
    (canonicalExposedEmbedding du dv k)
    (canonicalOutsideEmbedding du dv k)
    (canonicalExposedOutside_disjoint du dv k) hc restrictions hunsat

/-- The hard mixed high-overlap branch has an exact Lean-generated `K₄₁`
inner formula. -/
theorem canonicalK41OutsideListBendersClause_of_lrat
    (c : EdgeColoring (CanonicalAttachingVertex 15 16 13) FourColor)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List
      (OutsidePairColorRestriction (Fin 41) FourColor))
    (hunsat : (OutsideCoreCNF.outsideCoreFmla 41 4
      OutsideCoreCNF.fourColorEquivFin4 restrictions).proof []) :
    OutsideListBendersClause (canonicalExposedIncidence c)
      restrictions.toFinset := by
  exact canonicalOutsideListBendersClause_of_lrat c hc restrictions hunsat

namespace FiniteObstructionInterface

/-- Every finite obstruction interface inherits the canonical outside-list
cut for each semantically uncolourable core on its exact outside type. -/
theorem canonicalOutsideListBendersClause
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : EdgeColoring V FourColor} {hc : NoMonochromaticTriangle c}
    {delta : FourColor} {u v : V}
    (interface : FiniteObstructionInterface c hc delta u v)
    (core : Finset
      (OutsidePairColorRestriction
        (CanonicalOutsideVertex
          (colorDegree c delta u)
          (colorDegree c delta v)
          (Finset.card (colorNeighborhood c delta u ∩
            colorNeighborhood c delta v)))
        FourColor))
    (hcore : OutsideRestrictionCoreUnsatisfiable core) :
    OutsideListBendersClause
      (canonicalExposedIncidence interface.canonicalColoring) core := by
  exact canonicalOutsideListBendersClause_of_coreUnsatisfiable
    interface.canonicalColoring interface.canonicalColoring_noMono core hcore

end FiniteObstructionInterface

#print axioms R4333.canonicalExposedOutside_disjoint
#print axioms R4333.canonicalOutsideVertex_card_15_16_13
#print axioms R4333.canonicalExposedVertex_card_15_16_13
#print axioms R4333.canonicalOutside_edge_ne_of_collision
#print axioms R4333.canonicalOutsideListBendersClause_of_coreUnsatisfiable
#print axioms R4333.canonicalOutsideListBendersClause_of_lrat
#print axioms R4333.canonicalK41OutsideListBendersClause_of_lrat
#print axioms R4333.FiniteObstructionInterface.canonicalOutsideListBendersClause

end R4333
