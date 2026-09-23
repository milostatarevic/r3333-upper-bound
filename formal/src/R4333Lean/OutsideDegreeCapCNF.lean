import R4333Lean.CanonicalOutsideBenders
import R4333Lean.SequentialAtMostCNF

/-!
# Degree-capped outside cores

An outside-list core can be strengthened by the global colour-degree bound.
For one outside vertex `x` and colour `q`, this file gives an authoritative,
duplicate-free list of the canonical `K_n` edge atoms incident with `x`.
Under the colouring valuation, its true-input count is exactly the
`q`-degree of `x` in the induced outside colouring.

A selected finite set of exposed centres already joined to `x` in colour
`q` consumes the same number of slots in the host `q`-degree.  Disjointness
of the exposed and outside embeddings therefore gives

`selected.card + outsideDegree <= hostDegree`.

The final formula appends one Lean-defined sequential counter to an outside
core.  A checked LRAT refutation yields the cap-aware Benders clause: either
one core restriction is available, or one selected exposed incidence is not
actually colour `q`.
-/

namespace R4333

open FiniteColorCNF

namespace OutsideDegreeCapCNF

/-! ## Canonical incident-edge atoms -/

/-- The canonical unordered `K_n` atom for the edge `{x,y}` in colour `q`.
For distinct endpoints the smaller vertex number is always first, exactly
matching `FiniteColorCNF.edges`. -/
def outsideIncidentEdgeAtom {n k : Nat}
    (x y : Fin n) (q : Fin k) : Nat :=
  edgeAtom (min x.val y.val) (max x.val y.val) q.val

/-- For a fixed endpoint and colour, canonical incident-edge atoms are
injective in the other endpoint. -/
theorem outsideIncidentEdgeAtom_injective
    {n k : Nat} (x : Fin n) (q : Fin k) :
    Function.Injective (fun y : Fin n => outsideIncidentEdgeAtom x y q) := by
  intro y z h
  have hpairs :
      Nat.pair (min x.val y.val) (max x.val y.val) =
        Nat.pair (min x.val z.val) (max x.val z.val) :=
    (Nat.pair_eq_pair.mp
      (show Nat.pair
          (Nat.pair (min x.val y.val) (max x.val y.val)) q.val =
        Nat.pair
          (Nat.pair (min x.val z.val) (max x.val z.val)) q.val by
        simpa [outsideIncidentEdgeAtom, edgeAtom] using h)).1
  have hcoordinates := Nat.pair_eq_pair.mp hpairs
  have hsumY : min x.val y.val + max x.val y.val = x.val + y.val :=
    min_add_max x.val y.val
  have hsumZ : min x.val z.val + max x.val z.val = x.val + z.val :=
    min_add_max x.val z.val
  apply Fin.ext
  omega

/-- The authoritative counter inputs: one canonical atom for every outside
vertex other than `x`, in `Fin` order. -/
def outsideIncidentAtoms {n k : Nat} (x : Fin n) (q : Fin k) : List Nat :=
  ((List.finRange n).filter fun y => y ≠ x).map fun y =>
    outsideIncidentEdgeAtom x y q

/-- The input list contains no duplicate SAT atom. -/
theorem outsideIncidentAtoms_nodup
    {n k : Nat} (x : Fin n) (q : Fin k) :
    (outsideIncidentAtoms x q).Nodup := by
  unfold outsideIncidentAtoms
  exact ((List.nodup_finRange n).filter _).map
    (outsideIncidentEdgeAtom_injective x q)

/-- There is exactly one input for every other outside vertex. -/
theorem outsideIncidentAtoms_length
    {n k : Nat} (x : Fin n) (q : Fin k) :
    (outsideIncidentAtoms x q).length = n - 1 := by
  let candidates := (List.finRange n).filter fun y => y ≠ x
  have hnodup : candidates.Nodup := (List.nodup_finRange n).filter _
  have hfinset : candidates.toFinset = Finset.univ.erase x := by
    ext y
    simp [candidates]
  rw [outsideIncidentAtoms, List.length_map]
  change candidates.length = n - 1
  rw [← List.toFinset_card_of_nodup hnodup, hfinset]
  simp

@[simp] theorem outsideIncidentAtoms_length_41
    (x : Fin 41) (q : Fin 4) :
    (outsideIncidentAtoms x q).length = 40 := by
  simpa using outsideIncidentAtoms_length x q

@[simp] theorem mem_outsideIncidentAtoms_iff
    {n k : Nat} (x : Fin n) (q : Fin k) (atom : Nat) :
    atom ∈ outsideIncidentAtoms x q ↔
      ∃ y : Fin n, y ≠ x ∧ atom = outsideIncidentEdgeAtom x y q := by
  simp only [outsideIncidentAtoms, List.mem_map, List.mem_filter,
    List.mem_finRange, true_and]
  constructor
  · rintro ⟨y, hyne, h⟩
    exact ⟨y, of_decide_eq_true hyne, h.symm⟩
  · rintro ⟨y, hyne, rfl⟩
    exact ⟨y, by simpa using hyne, rfl⟩

/-- The canonical atom decodes to the actual edge colour under the standard
colouring valuation. -/
theorem coloringValuation_outsideIncidentEdgeAtom
    {n k : Nat} (d : EdgeColoring (Fin n) (Fin k))
    (x y : Fin n) (hxy : x ≠ y) (q : Fin k) :
    coloringValuation d (outsideIncidentEdgeAtom x y q) ↔ d x y = q := by
  by_cases hlt : x.val < y.val
  · have hmin : min x.val y.val = x.val := Nat.min_eq_left (Nat.le_of_lt hlt)
    have hmax : max x.val y.val = y.val := Nat.max_eq_right (Nat.le_of_lt hlt)
    simp [outsideIncidentEdgeAtom, hmin, hmax]
  · have hyx : y.val < x.val := by
      have hvals : x.val ≠ y.val := by
        intro h
        exact hxy (Fin.ext h)
      omega
    have hmin : min x.val y.val = y.val := Nat.min_eq_right (Nat.le_of_lt hyx)
    have hmax : max x.val y.val = x.val := Nat.max_eq_left (Nat.le_of_lt hyx)
    rw [outsideIncidentEdgeAtom, hmin, hmax,
      coloringValuation_edgeAtom, d.color_symm]

/-! ## Exact mathematical meaning of the true atom count -/

/-- The list of actual `q`-neighbours of `x`, in the same vertex order as
the authoritative input list. -/
def outsideColorNeighborList {n : Nat} {C : Type*} [DecidableEq C]
    (d : EdgeColoring (Fin n) C) (x : Fin n) (q : C) : List (Fin n) :=
  (List.finRange n).filter fun y => y ≠ x ∧ d x y = q

theorem outsideColorNeighborList_nodup
    {n : Nat} {C : Type*} [DecidableEq C]
    (d : EdgeColoring (Fin n) C) (x : Fin n) (q : C) :
    (outsideColorNeighborList d x q).Nodup :=
  (List.nodup_finRange n).filter _

/-- The ordered neighbour list represents exactly `colorNeighborhood`. -/
theorem outsideColorNeighborList_toFinset
    {n : Nat} {C : Type*} [DecidableEq C]
    (d : EdgeColoring (Fin n) C) (x : Fin n) (q : C) :
    (outsideColorNeighborList d x q).toFinset =
      colorNeighborhood d q x := by
  ext y
  simp [outsideColorNeighborList, mem_colorNeighborhood]

theorem outsideColorNeighborList_length
    {n : Nat} {C : Type*} [DecidableEq C]
    (d : EdgeColoring (Fin n) C) (x : Fin n) (q : C) :
    (outsideColorNeighborList d x q).length = colorDegree d q x := by
  rw [← List.toFinset_card_of_nodup
      (outsideColorNeighborList_nodup d x q),
    outsideColorNeighborList_toFinset]
  rfl

/-- The number of true incident input atoms is exactly the mathematical
outside colour degree. -/
theorem trueInputCount_outsideIncidentAtoms
    {n k : Nat} {C : Type*} [DecidableEq C]
    (palette : C ≃ Fin k) (d : EdgeColoring (Fin n) C)
    (x : Fin n) (q : C) :
    SequentialAtMostCNF.trueInputCount
        (coloringValuation (OutsideCoreCNF.paletteMappedColoring palette d))
        (outsideIncidentAtoms x (palette q)) =
      colorDegree d q x := by
  let candidates := (List.finRange n).filter fun y => y ≠ x
  have hbit : ∀ y : Fin n, y ≠ x →
      SequentialAtMostCNF.truthBit
          (coloringValuation
            (OutsideCoreCNF.paletteMappedColoring palette d))
          (outsideIncidentEdgeAtom x y (palette q)) =
        decide (d x y = q) := by
    intro y hxy
    apply Bool.eq_iff_iff.mpr
    rw [SequentialAtMostCNF.truthBit_eq_true]
    simp only [decide_eq_true_eq]
    rw [coloringValuation_outsideIncidentEdgeAtom _ x y hxy.symm]
    exact palette.injective.eq_iff
  change List.countP
      (SequentialAtMostCNF.truthBit
        (coloringValuation
          (OutsideCoreCNF.paletteMappedColoring palette d)))
      (candidates.map fun y => outsideIncidentEdgeAtom x y (palette q)) =
    colorDegree d q x
  rw [List.countP_map]
  have hcandidates : ∀ y ∈ candidates, y ≠ x := by
    intro y hy
    exact of_decide_eq_true (List.mem_filter.mp hy).2
  have hcount :
      List.countP
          (SequentialAtMostCNF.truthBit
            (coloringValuation
              (OutsideCoreCNF.paletteMappedColoring palette d)) ∘
            fun y => outsideIncidentEdgeAtom x y (palette q)) candidates =
        List.countP (fun y => decide (d x y = q)) candidates := by
    let f : Fin n → Bool :=
      SequentialAtMostCNF.truthBit
          (coloringValuation
            (OutsideCoreCNF.paletteMappedColoring palette d)) ∘
        fun y => outsideIncidentEdgeAtom x y (palette q)
    let g : Fin n → Bool := fun y => decide (d x y = q)
    have hgeneral : ∀ l : List (Fin n),
        (∀ y ∈ l, y ≠ x) → List.countP f l = List.countP g l := by
      intro l hl
      induction l with
      | nil => rfl
      | cons y ys ih =>
          have hy : y ≠ x := hl y (List.Mem.head _)
          have hys : ∀ z ∈ ys, z ≠ x := by
            intro z hz
            exact hl z (List.Mem.tail y hz)
          rw [List.countP_cons, List.countP_cons, ih hys]
          have hfg : f y = g y := by
            exact hbit y hy
          rw [hfg]
    exact hgeneral candidates hcandidates
  rw [hcount, List.countP_eq_length_filter]
  change ((candidates.filter fun y => decide (d x y = q))).length = _
  have hlists :
      candidates.filter (fun y => decide (d x y = q)) =
        outsideColorNeighborList d x q := by
    simp [candidates, outsideColorNeighborList, List.filter_filter,
      Bool.and_comm]
  rw [hlists, outsideColorNeighborList_length]

/-! ## Spending host-degree slots on selected exposed incidences -/

/-- Every selected exposed centre is asserted to meet `x` in colour `q`.
This is the positive outer assumption consumed by the cap-aware cut. -/
def SelectedExposedIncidencesHold
    {V E O C : Type*} (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : O ↪ V)
    (selected : Finset E) (x : O) (q : C) : Prop :=
  ∀ center ∈ selected, c (exposed center) (outside x) = q

/-- Images of the selected exposed centres and of all outside `q`-neighbours
inject disjointly into the host `q`-neighbourhood. -/
theorem selectedCard_add_outsideDegree_le_hostDegree
    {V E C : Type*} {n : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [DecidableEq C]
    (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (selected : Finset E) (x : Fin n) (q : C)
    (hselected : SelectedExposedIncidencesHold
      c exposed outside selected x q) :
    selected.card + colorDegree (outsideInducedColoring c outside) q x ≤
      colorDegree c q (outside x) := by
  let outsideNeighbors :=
    colorNeighborhood (outsideInducedColoring c outside) q x
  let outsideImage : Finset V := outsideNeighbors.map outside
  let selectedImage : Finset V := selected.map exposed
  have himagesDisjoint : Disjoint selectedImage outsideImage := by
    apply Finset.disjoint_left.mpr
    intro z hzSelected hzOutside
    obtain ⟨center, hcenter, hcenterEq⟩ :=
      Finset.mem_map.mp hzSelected
    obtain ⟨y, hy, hyEq⟩ := Finset.mem_map.mp hzOutside
    exact hdisjoint center y (hcenterEq.trans hyEq.symm)
  have hunionSubset : selectedImage ∪ outsideImage ⊆
      colorNeighborhood c q (outside x) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzSelected | hzOutside
    · obtain ⟨center, hcenter, rfl⟩ := Finset.mem_map.mp hzSelected
      apply (mem_colorNeighborhood c q (outside x) (exposed center)).mpr
      refine ⟨hdisjoint center x, ?_⟩
      rw [c.color_symm]
      exact hselected center hcenter
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hzOutside
      have hy' := (mem_colorNeighborhood
        (outsideInducedColoring c outside) q x y).mp hy
      apply (mem_colorNeighborhood c q (outside x) (outside y)).mpr
      exact ⟨outside.injective.ne hy'.1, hy'.2⟩
  have hselectedCard : selectedImage.card = selected.card := by
    simp [selectedImage]
  have houtsideCard : outsideImage.card =
      colorDegree (outsideInducedColoring c outside) q x := by
    simp [outsideImage, outsideNeighbors, colorDegree]
  calc
    selected.card + colorDegree (outsideInducedColoring c outside) q x =
        selectedImage.card + outsideImage.card := by
      rw [hselectedCard, houtsideCard]
    _ = (selectedImage ∪ outsideImage).card := by
      rw [Finset.card_union_of_disjoint himagesDisjoint]
    _ ≤ (colorNeighborhood c q (outside x)).card :=
      Finset.card_le_card hunionSubset
    _ = colorDegree c q (outside x) := rfl

/-- Subtraction form used as the sequential-counter bound. -/
theorem outsideDegree_le_hostBound_sub_selectedCard
    {V E C : Type*} {n hostBound : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [DecidableEq C]
    (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (selected : Finset E) (x : Fin n) (q : C)
    (hselected : SelectedExposedIncidencesHold
      c exposed outside selected x q)
    (hhost : colorDegree c q (outside x) ≤ hostBound) :
    colorDegree (outsideInducedColoring c outside) q x ≤
      hostBound - selected.card := by
  have hsum := selectedCard_add_outsideDegree_le_hostDegree
    c exposed outside hdisjoint selected x q hselected
  omega

/-- In a triangle-free four-colouring, the universal host cap is 16, so
selected exposed incidences immediately leave at most
`16 - selected.card` outside neighbours of that colour. -/
theorem outsideFourColorDegree_le_sixteen_sub_selectedCard
    {V E : Type*} {n : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (c : EdgeColoring V FourColor)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (selected : Finset E) (x : Fin n) (q : FourColor)
    (hselected : SelectedExposedIncidencesHold
      c exposed outside selected x q) :
    colorDegree (outsideInducedColoring c outside) q x ≤
      16 - selected.card := by
  exact outsideDegree_le_hostBound_sub_selectedCard
    c exposed outside hdisjoint selected x q hselected
      (fourColor_colorDegree_le_sixteen c hc q (outside x))

/-- The requested uncoupled special case: an induced outside colour degree
never exceeds the full host colour degree. -/
theorem outsideDegree_le_hostDegree
    {V C : Type*} {n : Nat}
    [Fintype V] [DecidableEq V] [DecidableEq C]
    (c : EdgeColoring V C) (outside : Fin n ↪ V)
    (x : Fin n) (q : C) :
    colorDegree (outsideInducedColoring c outside) q x ≤
      colorDegree c q (outside x) := by
  let emptyExposed : Empty ↪ V := {
    toFun e := nomatch e
    inj' e := nomatch e
  }
  have hdisjoint : ExposedOutsideDisjoint emptyExposed outside := by
    intro e
    exact nomatch e
  simpa [SelectedExposedIncidencesHold] using
    selectedCard_add_outsideDegree_le_hostDegree
      c emptyExposed outside hdisjoint (∅ : Finset Empty) x q
        (by intro center; exact nomatch center)

/-! ## A counter namespace disjoint from all `K_n` edge atoms -/

/-- Consecutive degree-counter tags begin at `n²`, above every leading
endpoint-pair code of `K_n`.  The `(x,q)` offset makes all vertex/colour
counters distinct while keeping the namespace dense. -/
def outsideDegreeCounterTag {n k : Nat} (x : Fin n) (q : Fin k) : Nat :=
  n * n + (x.val * k + q.val)

/-- Distinct vertex/colour pairs receive distinct consecutive tags. -/
theorem outsideDegreeCounterTag_injective
    {n k : Nat} {x y : Fin n} {q r : Fin k}
    (h : outsideDegreeCounterTag x q = outsideDegreeCounterTag y r) :
    x = y ∧ q = r := by
  have hoffset : x.val * k + q.val = y.val * k + r.val := by
    exact Nat.add_left_cancel h
  have hmod := congrArg (fun value => value % k) hoffset
  have hqval : q.val = r.val := by
    simpa [Nat.add_comm, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt q.isLt, Nat.mod_eq_of_lt r.isLt] using hmod
  have hmul : x.val * k = y.val * k := by omega
  have hxval : x.val = y.val := by
    have hk : 0 < k := by omega
    exact Nat.mul_right_cancel hk hmul
  exact ⟨Fin.ext hxval, Fin.ext hqval⟩

theorem outsideDegreeCounterTag_pair_injective
    {n k : Nat} :
    Function.Injective
      (fun pair : Fin n × Fin k =>
        outsideDegreeCounterTag pair.1 pair.2) := by
  rintro ⟨x, q⟩ ⟨y, r⟩ h
  obtain ⟨rfl, rfl⟩ := outsideDegreeCounterTag_injective h
  rfl

private theorem pair_lt_vertexSquare
    {n a b : Nat} (ha : a < n) (hb : b < n) : Nat.pair a b < n * n := by
  have hmax : max a b + 1 ≤ n := by
    rw [Nat.add_one_le_iff]
    exact max_lt ha hb
  calc
    Nat.pair a b < (max a b + 1) ^ 2 :=
      Nat.pair_lt_max_add_one_sq a b
    _ ≤ n ^ 2 := Nat.pow_le_pow_left hmax 2
    _ = n * n := by simp [Nat.pow_two]

theorem edgeAtom_outside_counterNamespace
    {n k a b r : Nat} (x : Fin n) (q : Fin k)
    (ha : a < n) (hb : b < n) :
    ¬SequentialAtMostCNF.InSequentialNamespace
      (outsideDegreeCounterTag x q) (edgeAtom a b r) := by
  simp only [SequentialAtMostCNF.InSequentialNamespace,
    outsideDegreeCounterTag, edgeAtom, Nat.unpair_pair]
  intro h
  have hpairLt := pair_lt_vertexSquare ha hb
  omega

/-- Every authoritative incident input lies outside every degree-counter
namespace for the same `K_n`, not only its own counter namespace. -/
theorem outsideIncidentAtoms_outside_counterNamespace_for
    {n k : Nat} (reservedX : Fin n) (reservedQ : Fin k)
    (targetX : Fin n) (targetQ : Fin k) :
    SequentialAtMostCNF.InputsOutsideNamespace
      (outsideDegreeCounterTag reservedX reservedQ)
      (outsideIncidentAtoms targetX targetQ) := by
  intro atom hatom
  obtain ⟨y, _hyx, rfl⟩ :=
    (mem_outsideIncidentAtoms_iff targetX targetQ atom).mp hatom
  apply edgeAtom_outside_counterNamespace reservedX reservedQ
  · exact lt_of_le_of_lt (Nat.min_le_left targetX.val y.val) targetX.isLt
  · exact max_lt targetX.isLt y.isLt

/-- Own-namespace specialization used by the single-counter formula. -/
theorem outsideIncidentAtoms_outside_counterNamespace
    {n k : Nat} (x : Fin n) (q : Fin k) :
    SequentialAtMostCNF.InputsOutsideNamespace
      (outsideDegreeCounterTag x q) (outsideIncidentAtoms x q) :=
  outsideIncidentAtoms_outside_counterNamespace_for x q x q

private theorem edge_members_bounds
    {n a b : Nat} (h : (a, b) ∈ edges n) :
    a < n ∧ b < n ∧ a < b := by
  simp only [edges, List.mem_flatMap, List.mem_map] at h
  obtain ⟨a', ha', b', hb', hp⟩ := h
  have ha'lt : a' < n := by simpa [vertices] using ha'
  have hb'mem : b' ∈ vertices n := (List.mem_filter.mp hb').1
  have hb'lt : b' < n := by simpa [vertices] using hb'mem
  have hab' : a' < b' := of_decide_eq_true (List.mem_filter.mp hb').2
  injection hp with haa hbb
  subst a'
  subst b'
  exact ⟨ha'lt, hb'lt, hab'⟩

/-- The safe tag is disjoint from every atom in the canonical colouring
base formula. -/
theorem goodColoringFmla_outside_counterNamespace
    {n k : Nat} (x : Fin n) (counterColor : Fin k) :
    SequentialAtMostCNF.FormulaOutsideNamespace
      (outsideDegreeCounterTag x counterColor) (goodColoringFmla n k) := by
  intro clause hclause literal hliteral
  have hclause' : clause ∈ goodColoringFmla n k := hclause
  simp only [goodColoringFmla, List.mem_append] at hclause'
  rcases hclause' with (hatLeast | hatMost) | htriangle
  · simp only [atLeastOneClauses, List.mem_map] at hatLeast
    obtain ⟨⟨a, b⟩, hedge, rfl⟩ := hatLeast
    change List.Mem literal
      ((List.range k).map fun q => Sat.Literal.pos (edgeAtom a b q))
      at hliteral
    have hliteral' : literal ∈
        ((List.range k).map fun q => Sat.Literal.pos (edgeAtom a b q)) :=
      hliteral
    simp only [List.mem_map] at hliteral'
    obtain ⟨q, _hq, rfl⟩ := hliteral'
    exact edgeAtom_outside_counterNamespace x counterColor
      (edge_members_bounds hedge).1 (edge_members_bounds hedge).2.1
  · simp only [atMostOneClauses, List.mem_flatMap,
      List.mem_map] at hatMost
    obtain ⟨⟨a, b⟩, hedge, ⟨⟨q, r⟩, _hqr, rfl⟩⟩ := hatMost
    change List.Mem literal
      [Sat.Literal.neg (edgeAtom a b q),
        Sat.Literal.neg (edgeAtom a b r)] at hliteral
    have hliteral' : literal ∈
        [Sat.Literal.neg (edgeAtom a b q),
          Sat.Literal.neg (edgeAtom a b r)] := hliteral
    simp at hliteral'
    rcases hliteral' with rfl | rfl
    · exact edgeAtom_outside_counterNamespace x counterColor
        (edge_members_bounds hedge).1 (edge_members_bounds hedge).2.1
    · exact edgeAtom_outside_counterNamespace x counterColor
        (edge_members_bounds hedge).1 (edge_members_bounds hedge).2.1
  · simp only [triangleClauses, List.mem_flatMap,
      List.mem_map] at htriangle
    obtain ⟨⟨a, b, d⟩, htriple, ⟨q, _hq, rfl⟩⟩ := htriangle
    obtain ⟨ha, hb, _hd, _hab, _hbd⟩ := mem_triples_iff_bounds htriple
    change List.Mem literal
      [Sat.Literal.neg (edgeAtom a b q),
        Sat.Literal.neg (edgeAtom a d q),
        Sat.Literal.neg (edgeAtom b d q)] at hliteral
    have hliteral' : literal ∈
        [Sat.Literal.neg (edgeAtom a b q),
          Sat.Literal.neg (edgeAtom a d q),
          Sat.Literal.neg (edgeAtom b d q)] := hliteral
    simp at hliteral'
    rcases hliteral' with rfl | rfl | rfl
    · exact edgeAtom_outside_counterNamespace x counterColor ha hb
    · exact edgeAtom_outside_counterNamespace x counterColor ha _hd
    · exact edgeAtom_outside_counterNamespace x counterColor hb _hd

/-- Restriction units also mention only in-range outside edge atoms. -/
theorem restrictionClauses_outside_counterNamespace
    {n k : Nat} {C : Type*}
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (x : Fin n) (q : Fin k) :
    SequentialAtMostCNF.FormulaOutsideNamespace
      (outsideDegreeCounterTag x q)
      (OutsideCoreCNF.restrictionClauses palette restrictions) := by
  intro clause hclause literal hliteral
  have hclause' : clause ∈
      OutsideCoreCNF.restrictionClauses palette restrictions := hclause
  simp only [OutsideCoreCNF.restrictionClauses, List.mem_map] at hclause'
  obtain ⟨restriction, _hrestriction, rfl⟩ := hclause'
  change List.Mem literal
    [Sat.Literal.neg (OutsideCoreCNF.restrictionAtom palette restriction)]
    at hliteral
  have hliteral' : literal ∈
      [Sat.Literal.neg (OutsideCoreCNF.restrictionAtom palette restriction)] :=
    hliteral
  simp only [List.mem_singleton] at hliteral'
  have hliteral := hliteral'
  subst literal
  exact edgeAtom_outside_counterNamespace x q
    restriction.left.isLt restriction.right.isLt

/-- Hence the entire outside-core base formula is protected from the
counter's auxiliary namespace. -/
theorem outsideCoreFmla_outside_counterNamespace
    {n k : Nat} {C : Type*}
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (x : Fin n) (q : Fin k) :
    SequentialAtMostCNF.FormulaOutsideNamespace
      (outsideDegreeCounterTag x q)
      (OutsideCoreCNF.outsideCoreFmla n k palette restrictions) := by
  intro clause hclause literal hliteral
  rcases List.mem_append.mp hclause with hbase | hrestrictions
  · exact goodColoringFmla_outside_counterNamespace x q
      clause hbase literal hliteral
  · exact restrictionClauses_outside_counterNamespace
      palette restrictions x q
      clause hrestrictions literal hliteral

/-! ## One capped outside core and its checked semantic boundary -/

/-- Append one authoritative incident-edge at-most counter to the outside
core.  Clause order is the complete outside core first, followed by the
sequential counter in `SequentialAtMostCNF` order. -/
def outsideCoreWithDegreeCapFmla
    {C : Type*} (n k : Nat) (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (x : Fin n) (q : Fin k) (bound : Nat) : Sat.Fmla :=
  SequentialAtMostCNF.withSequentialAtMost
    (OutsideCoreCNF.outsideCoreFmla n k palette restrictions)
    (outsideDegreeCounterTag x q) bound (outsideIncidentAtoms x q)

/-- Semantic meaning of an uncolourable degree-capped restriction core. -/
def OutsideRestrictionCoreUnsatisfiableWithDegreeCap
    {n : Nat} {C : Type*} [DecidableEq C]
    (core : Finset (OutsidePairColorRestriction (Fin n) C))
    (x : Fin n) (q : C) (bound : Nat) : Prop :=
  ¬∃ d : EdgeColoring (Fin n) C,
    NoMonochromaticTriangle d ∧
      OutsideColoringAvoidsCore d core ∧
      colorDegree d q x ≤ bound

/-- A checked LRAT refutation of the exact capped formula proves its
mathematical degree-capped core is uncolourable. -/
theorem cappedCoreUnsatisfiable_of_lrat
    {n k : Nat} {C : Type*} [DecidableEq C]
    (palette : C ≃ Fin k)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (x : Fin n) (q : C) (bound : Nat)
    (hunsat : (outsideCoreWithDegreeCapFmla n k palette restrictions
      x (palette q) bound).proof []) :
    OutsideRestrictionCoreUnsatisfiableWithDegreeCap
      restrictions.toFinset x q bound := by
  rintro ⟨d, hd, havoids, hdegree⟩
  let valuation := coloringValuation
    (OutsideCoreCNF.paletteMappedColoring palette d)
  have hbase : valuation.satisfies_fmla
      (OutsideCoreCNF.outsideCoreFmla n k palette restrictions) := by
    exact OutsideCoreCNF.coloring_satisfies_outsideCoreFmla
      palette restrictions d hd havoids
  have hatMost : SequentialAtMostCNF.InputsAtMost bound
      (outsideIncidentAtoms x (palette q)) valuation := by
    unfold SequentialAtMostCNF.InputsAtMost
    rw [trueInputCount_outsideIncidentAtoms palette d x q]
    exact hdegree
  have hnoModel := SequentialAtMostCNF.no_base_valuation_atMost_of_lrat
    (OutsideCoreCNF.outsideCoreFmla n k palette restrictions)
    (outsideDegreeCounterTag x (palette q)) bound
    (outsideIncidentAtoms x (palette q))
    (outsideCoreFmla_outside_counterNamespace
      palette restrictions x (palette q))
    (outsideIncidentAtoms_outside_counterNamespace x (palette q))
    hunsat
  exact hnoModel ⟨valuation, hbase, hatMost⟩

/-! ## The cap-aware learned Benders clause -/

/-- Either one restriction-core colour is available, or one of the selected
positive exposed incidences used to justify the degree cap is false. -/
def OutsideDegreeCapBendersClause
    {E O C : Type*} [DecidableEq O] [DecidableEq C]
    (incidence : ExposedIncidence E O C)
    (core : Finset (OutsidePairColorRestriction O C))
    (selected : Finset E) (x : O) (q : C) : Prop :=
  OutsideListBendersClause incidence core ∨
    ∃ center ∈ selected, incidence center x ≠ q

/-- Semantic cap-aware Benders soundness.  If all core collisions and all
selected incidences held, the actual induced outside colouring would avoid
the core and satisfy the degree cap, contradicting capped-core
uncolourability. -/
theorem outsideDegreeCapBendersClause_of_cappedCoreUnsatisfiable
    {V E C : Type*} {n hostBound : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [DecidableEq C]
    (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (core : Finset (OutsidePairColorRestriction (Fin n) C))
    (selected : Finset E) (x : Fin n) (q : C)
    (hhost : colorDegree c q (outside x) ≤ hostBound)
    (hcore : OutsideRestrictionCoreUnsatisfiableWithDegreeCap
      core x q (hostBound - selected.card)) :
    OutsideDegreeCapBendersClause
      (coloringExposedIncidence c exposed outside)
      core selected x q := by
  classical
  by_contra hclause
  have hallCollide : ∀ restriction ∈ core,
      restriction.collides
        (coloringExposedIncidence c exposed outside) := by
    intro restriction hrestriction
    by_contra hcollision
    apply hclause
    left
    exact ⟨restriction, hrestriction, hcollision⟩
  have hselected : SelectedExposedIncidencesHold
      c exposed outside selected x q := by
    intro center hcenter
    by_contra hincidence
    apply hclause
    right
    exact ⟨center, hcenter, hincidence⟩
  apply hcore
  refine ⟨outsideInducedColoring c outside,
    noMono_outsideInducedColoring c outside hc, ?_, ?_⟩
  · exact outsideInducedColoring_avoidsCore_of_all_collide
      c exposed outside hdisjoint hc core hallCollide
  · exact outsideDegree_le_hostBound_sub_selectedCard
      c exposed outside hdisjoint selected x q hselected hhost

/-- End-to-end checked cap-aware cut from one Lean-generated formula and
one kernel-checked LRAT proof. -/
theorem outsideDegreeCapBendersClause_of_lrat
    {V E C : Type*} {n k hostBound : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [DecidableEq C]
    (palette : C ≃ Fin k)
    (c : EdgeColoring V C)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List (OutsidePairColorRestriction (Fin n) C))
    (selected : Finset E) (x : Fin n) (q : C)
    (hhost : colorDegree c q (outside x) ≤ hostBound)
    (hunsat : (outsideCoreWithDegreeCapFmla n k palette restrictions
      x (palette q) (hostBound - selected.card)).proof []) :
    OutsideDegreeCapBendersClause
      (coloringExposedIncidence c exposed outside)
      restrictions.toFinset selected x q := by
  exact outsideDegreeCapBendersClause_of_cappedCoreUnsatisfiable
    c exposed outside hdisjoint hc restrictions.toFinset selected x q hhost
    (cappedCoreUnsatisfiable_of_lrat
      palette restrictions x q (hostBound - selected.card) hunsat)

/-- Four-colour specialization: the proved universal degree bound 16
discharges the only host-cap premise. -/
theorem outsideFourColorDegreeCapBendersClause_of_lrat
    {V E : Type*} {n : Nat}
    [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (c : EdgeColoring V FourColor)
    (exposed : E ↪ V) (outside : Fin n ↪ V)
    (hdisjoint : ExposedOutsideDisjoint exposed outside)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List
      (OutsidePairColorRestriction (Fin n) FourColor))
    (selected : Finset E) (x : Fin n) (q : FourColor)
    (hunsat : (outsideCoreWithDegreeCapFmla n 4
      OutsideCoreCNF.fourColorEquivFin4 restrictions
      x (OutsideCoreCNF.fourColorEquivFin4 q)
      (16 - selected.card)).proof []) :
    OutsideDegreeCapBendersClause
      (coloringExposedIncidence c exposed outside)
      restrictions.toFinset selected x q := by
  exact outsideDegreeCapBendersClause_of_lrat
    OutsideCoreCNF.fourColorEquivFin4 c exposed outside hdisjoint hc
    restrictions selected x q
    (fourColor_colorDegree_le_sixteen c hc q (outside x)) hunsat

/-- Exact hard-branch specialization on the canonical exposed-20/outside-41
host. -/
theorem canonicalK41OutsideDegreeCapBendersClause_of_lrat
    (c : EdgeColoring (CanonicalAttachingVertex 15 16 13) FourColor)
    (hc : NoMonochromaticTriangle c)
    (restrictions : List
      (OutsidePairColorRestriction (Fin 41) FourColor))
    (selected : Finset (CanonicalExposedVertex 15 16 13))
    (x : Fin 41) (q : FourColor)
    (hunsat : (outsideCoreWithDegreeCapFmla 41 4
      OutsideCoreCNF.fourColorEquivFin4 restrictions
      x (OutsideCoreCNF.fourColorEquivFin4 q)
      (16 - selected.card)).proof []) :
    OutsideDegreeCapBendersClause (canonicalExposedIncidence c)
      restrictions.toFinset selected x q := by
  exact outsideFourColorDegreeCapBendersClause_of_lrat
    c (canonicalExposedEmbedding 15 16 13)
    (canonicalOutsideEmbedding 15 16 13)
    (canonicalExposedOutside_disjoint 15 16 13) hc
    restrictions selected x q hunsat

#print axioms R4333.OutsideDegreeCapCNF.trueInputCount_outsideIncidentAtoms
#print axioms R4333.OutsideDegreeCapCNF.selectedCard_add_outsideDegree_le_hostDegree
#print axioms R4333.OutsideDegreeCapCNF.outsideCoreFmla_outside_counterNamespace
#print axioms R4333.OutsideDegreeCapCNF.cappedCoreUnsatisfiable_of_lrat
#print axioms R4333.OutsideDegreeCapCNF.outsideDegreeCapBendersClause_of_lrat
#print axioms R4333.OutsideDegreeCapCNF.outsideFourColorDegreeCapBendersClause_of_lrat
#print axioms R4333.OutsideDegreeCapCNF.canonicalK41OutsideDegreeCapBendersClause_of_lrat

end OutsideDegreeCapCNF

end R4333
