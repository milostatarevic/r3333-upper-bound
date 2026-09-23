import R4333Lean.CriticalTemplates
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Data.Fintype.Powerset

/-!
# Constructive uniqueness infrastructure for `SRG(16,5,0,2)`

Fixing a root `r`, the five neighbours form `clebschA`; the ten remaining
vertices form `clebschB`.  A vertex in `clebschB` is sent to its two
neighbours in `clebschA`.  The lemmas below establish the cardinalities and
the incidence/adjacency facts used in the standard uniqueness proof.
-/

namespace R4333

open Finset

universe u

section StronglyRegular

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The five neighbours of a chosen root. -/
def clebschA (r : V) : Finset V := G.neighborFinset r

/-- The vertices different from and nonadjacent to the root. -/
def clebschB (r : V) : Finset V :=
  Finset.univ.filter fun v ↦ v ≠ r ∧ ¬G.Adj r v

omit [DecidableEq V] in
@[simp] theorem mem_clebschA {r v : V} :
    v ∈ clebschA G r ↔ G.Adj r v := by
  simp [clebschA]

@[simp] theorem mem_clebschB {r v : V} :
    v ∈ clebschB G r ↔ v ≠ r ∧ ¬G.Adj r v := by
  simp [clebschB]

omit [DecidableEq V] in
theorem card_clebschA
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    #(clebschA G r) = 5 := by
  simpa [clebschA] using h.regular.degree_eq r

omit [DecidableEq V] in
theorem root_not_mem_clebschA (r : V) : r ∉ clebschA G r := by
  simp

omit [DecidableEq V] in
theorem clebschA_pair_not_adj
    (h : G.IsSRGWith 16 5 0 2) {r x y : V}
    (hx : x ∈ clebschA G r) (hy : y ∈ clebschA G r) :
    ¬G.Adj x y := by
  intro hxy
  have hrx : G.Adj r x := by simpa [clebschA] using hx
  have hry : G.Adj r y := by simpa [clebschA] using hy
  have hzero := h.of_adj r x hrx
  have hymem : y ∈ G.commonNeighbors r x := by
    exact G.mem_commonNeighbors.mpr ⟨hry, hxy⟩
  exact (Fintype.card_eq_zero_iff.mp hzero).false ⟨y, hymem⟩

theorem card_clebschB
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    #(clebschB G r) = 10 := by
  have hcardV : Fintype.card V = 16 := h.card
  have hA : #(clebschA G r) = 5 := card_clebschA G h r
  have hpartition :
      clebschB G r = (Finset.univ \ insert r (clebschA G r)) := by
    ext v
    by_cases hvr : v = r
    · subst v
      simp
    · simp [clebschB, hvr, mem_clebschA]
  rw [hpartition, card_sdiff_of_subset (subset_univ _), card_univ,
    card_insert_of_notMem (root_not_mem_clebschA G r), hA, hcardV]

/-- The two neighbours in `A` of a vertex outside `A ∪ {r}`. -/
def clebschPairRaw (r b : V) : Finset V :=
  (G.commonNeighbors r b).toFinset

omit [DecidableEq V] in
theorem clebschPairRaw_subset_A {r b : V} :
    clebschPairRaw G r b ⊆ clebschA G r := by
  intro x hx
  have hx' : x ∈ G.commonNeighbors r b := by
    simpa [clebschPairRaw] using hx
  simpa [clebschA] using (G.mem_commonNeighbors.mp hx').1

theorem card_clebschPairRaw
    (h : G.IsSRGWith 16 5 0 2) {r b : V}
    (hb : b ∈ clebschB G r) :
    #(clebschPairRaw G r b) = 2 := by
  have hb' : b ≠ r ∧ ¬G.Adj r b := by simpa [clebschB] using hb
  have hcard := h.of_not_adj hb'.1.symm hb'.2
  simpa [clebschPairRaw, Set.toFinset_card] using hcard

/-- Package a `B` vertex's common-neighbour pair as a two-subset of `A`. -/
def clebschPair
    (h : G.IsSRGWith 16 5 0 2) (r : V) (b : ↥(clebschB G r)) :
    {s : Finset ↥(clebschA G r) // #s = 2} := by
  let raw := clebschPairRaw G r b
  let lifted : Finset ↥(clebschA G r) :=
    raw.subtype (fun x ↦ x ∈ clebschA G r)
  refine ⟨lifted, ?_⟩
  rw [Finset.card_subtype]
  have hsubset : raw ⊆ clebschA G r := clebschPairRaw_subset_A G
  rw [filter_eq_self.mpr hsubset]
  exact card_clebschPairRaw G h b.property

@[simp] theorem mem_clebschPair_iff
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (b : ↥(clebschB G r)) (a : ↥(clebschA G r)) :
    a ∈ (clebschPair G h r b : Finset ↥(clebschA G r)) ↔ G.Adj b a := by
  dsimp [clebschPair]
  rw [Finset.mem_subtype]
  change (a : V) ∈ (G.commonNeighbors r b).toFinset ↔ G.Adj b a
  rw [Set.mem_toFinset, G.mem_commonNeighbors]
  constructor
  · exact fun ha ↦ ha.2
  · intro hba
    have hra : G.Adj r (a : V) := by
      exact (G.mem_neighborFinset r (a : V)).mp a.property
    exact ⟨hra, hba⟩

theorem clebschPair_injective
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    Function.Injective (clebschPair G h r) := by
  intro b c hbc
  by_contra hne
  have hvalne : (b : V) ≠ (c : V) := by
    intro hv
    exact hne (Subtype.ext hv)
  obtain ⟨a₁, a₂, ha₁a₂, hpair⟩ :=
    Finset.card_eq_two.mp (clebschPair G h r b).property
  have ha₁mem_b : a₁ ∈ (clebschPair G h r b : Finset ↥(clebschA G r)) := by
    rw [hpair]
    simp
  have ha₂mem_b : a₂ ∈ (clebschPair G h r b : Finset ↥(clebschA G r)) := by
    rw [hpair]
    simp
  have hpairs :
      (clebschPair G h r b : Finset ↥(clebschA G r)) =
        (clebschPair G h r c : Finset ↥(clebschA G r)) :=
    congrArg Subtype.val hbc
  have ha₁mem_c : a₁ ∈ (clebschPair G h r c : Finset ↥(clebschA G r)) := by
    rw [← hpairs]
    exact ha₁mem_b
  have ha₂mem_c : a₂ ∈ (clebschPair G h r c : Finset ↥(clebschA G r)) := by
    rw [← hpairs]
    exact ha₂mem_b
  have hb₁ : G.Adj (b : V) (a₁ : V) :=
    (mem_clebschPair_iff G h r b a₁).mp ha₁mem_b
  have hb₂ : G.Adj (b : V) (a₂ : V) :=
    (mem_clebschPair_iff G h r b a₂).mp ha₂mem_b
  have hc₁ : G.Adj (c : V) (a₁ : V) :=
    (mem_clebschPair_iff G h r c a₁).mp ha₁mem_c
  have hc₂ : G.Adj (c : V) (a₂ : V) :=
    (mem_clebschPair_iff G h r c a₂).mp ha₂mem_c
  have hr₁ : G.Adj r (a₁ : V) := by
    exact (mem_clebschA G).mp a₁.property
  have hr₂ : G.Adj r (a₂ : V) := by
    exact (mem_clebschA G).mp a₂.property
  have ha_not_adj : ¬G.Adj (a₁ : V) (a₂ : V) :=
    clebschA_pair_not_adj G h a₁.property a₂.property
  have hcommon : Fintype.card (G.commonNeighbors (a₁ : V) (a₂ : V)) = 2 :=
    h.of_not_adj (by exact_mod_cast ha₁a₂) ha_not_adj
  have hsub :
      ({r, (b : V), (c : V)} : Finset V) ⊆
        (G.commonNeighbors (a₁ : V) (a₂ : V)).toFinset := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with (rfl | rfl | rfl)
    · exact Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hr₁.symm, hr₂.symm⟩)
    · exact Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hb₁.symm, hb₂.symm⟩)
    · exact Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hc₁.symm, hc₂.symm⟩)
  have hcard_le := Finset.card_le_card hsub
  have hbr : (b : V) ≠ r := (mem_clebschB G).mp b.property |>.1
  have hcr : (c : V) ≠ r := (mem_clebschB G).mp c.property |>.1
  have hleft : #({r, (b : V), (c : V)} : Finset V) = 3 := by
    simp [hvalne, Ne.symm hbr, Ne.symm hcr]
  have hright : #((G.commonNeighbors (a₁ : V) (a₂ : V)).toFinset) = 2 := by
    simpa [Set.toFinset_card] using hcommon
  omega

theorem card_clebschPair_source
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    Fintype.card ↥(clebschB G r) = 10 := by
  rw [Fintype.card_coe]
  exact card_clebschB G h r

omit [DecidableEq V] in
theorem card_clebschPair_target
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    Fintype.card {s : Finset ↥(clebschA G r) // #s = 2} = 10 := by
  rw [Fintype.card_finset_len, Fintype.card_coe, card_clebschA G h r]
  norm_num [Nat.choose]

theorem clebschPair_bijective
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    Function.Bijective (clebschPair G h r) := by
  apply (Fintype.bijective_iff_injective_and_card (clebschPair G h r)).mpr
  exact ⟨clebschPair_injective G h r,
    (card_clebschPair_source G h r).trans (card_clebschPair_target G h r).symm⟩

/-- The ten `B` vertices are canonically equivalent to the two-subsets of `A`. -/
noncomputable def clebschPairEquiv
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    ↥(clebschB G r) ≃ {s : Finset ↥(clebschA G r) // #s = 2} :=
  Equiv.ofBijective (clebschPair G h r) (clebschPair_bijective G h r)

@[simp] theorem clebschPairEquiv_apply
    (h : G.IsSRGWith 16 5 0 2) (r : V) (b : ↥(clebschB G r)) :
    clebschPairEquiv G h r b = clebschPair G h r b := rfl

/-- The neighbours of a `B` vertex which themselves lie in `B` (as vertices of `V`). -/
def clebschBNeighborVals (r : V) (b : ↥(clebschB G r)) : Finset V :=
  (clebschB G r).filter fun c ↦ G.Adj b c

@[simp] theorem mem_clebschBNeighborVals
    (r : V) (b : ↥(clebschB G r)) (c : V) :
    c ∈ clebschBNeighborVals G r b ↔ c ∈ clebschB G r ∧ G.Adj b c := by
  simp [clebschBNeighborVals]

theorem card_clebschBNeighborVals
    (h : G.IsSRGWith 16 5 0 2) (r : V) (b : ↥(clebschB G r)) :
    #(clebschBNeighborVals G r b) = 3 := by
  have hdecomp :
      G.neighborFinset b =
        clebschPairRaw G r b ∪ clebschBNeighborVals G r b := by
    ext x
    constructor
    · intro hbx
      have hbx' : G.Adj (b : V) x := by simpa using hbx
      by_cases hrx : G.Adj r x
      · apply Finset.mem_union_left
        exact Set.mem_toFinset.mpr (G.mem_commonNeighbors.mpr ⟨hrx, hbx'⟩)
      · apply Finset.mem_union_right
        have hxr : x ≠ r := by
          intro hxr
          subst x
          exact ((mem_clebschB G).mp b.property).2 hbx'.symm
        exact (mem_clebschBNeighborVals G r b x).mpr
          ⟨(mem_clebschB G).mpr ⟨hxr, hrx⟩, hbx'⟩
    · intro hx
      rcases Finset.mem_union.mp hx with hx | hx
      · have hx' := G.mem_commonNeighbors.mp (Set.mem_toFinset.mp hx)
        simpa using hx'.2
      · exact (G.mem_neighborFinset (b : V) x).mpr
          ((mem_clebschBNeighborVals G r b x).mp hx).2
  have hdisjoint :
      Disjoint (clebschPairRaw G r b) (clebschBNeighborVals G r b) := by
    rw [Finset.disjoint_left]
    intro x hxpair hxB
    have hrx : G.Adj r x :=
      (G.mem_commonNeighbors.mp (Set.mem_toFinset.mp hxpair)).1
    exact ((mem_clebschB G).mp ((mem_clebschBNeighborVals G r b x).mp hxB).1).2 hrx
  have hdegree : #(G.neighborFinset b) = 5 := h.regular.degree_eq b
  rw [hdecomp, Finset.card_union_of_disjoint hdisjoint,
    card_clebschPairRaw G h b.property] at hdegree
  omega

/-- Adjacent `B` vertices have disjoint pairs of neighbours in `A`. -/
theorem clebschPair_disjoint_of_adj
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (b c : ↥(clebschB G r)) (hbc : G.Adj b c) :
    Disjoint
      (clebschPair G h r b : Finset ↥(clebschA G r))
      (clebschPair G h r c : Finset ↥(clebschA G r)) := by
  rw [Finset.disjoint_left]
  intro a hab hac
  have hba : G.Adj (b : V) (a : V) :=
    (mem_clebschPair_iff G h r b a).mp hab
  have hca : G.Adj (c : V) (a : V) :=
    (mem_clebschPair_iff G h r c a).mp hac
  have hzero := h.of_adj (b : V) (c : V) hbc
  have hamem : (a : V) ∈ G.commonNeighbors (b : V) (c : V) :=
    G.mem_commonNeighbors.mpr ⟨hba, hca⟩
  exact (Fintype.card_eq_zero_iff.mp hzero).false ⟨a, hamem⟩

/-- Disjoint `A`-pairs force adjacency of the corresponding `B` vertices. -/
theorem clebschPair_adj_of_disjoint
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (b c : ↥(clebschB G r))
    (hdis : Disjoint
      (clebschPair G h r b : Finset ↥(clebschA G r))
      (clebschPair G h r c : Finset ↥(clebschA G r))) :
    G.Adj b c := by
  have hbcne : (b : V) ≠ (c : V) := by
    intro hbc
    have hsub : b = c := Subtype.ext hbc
    subst c
    have hempty : (clebschPair G h r b : Finset ↥(clebschA G r)) = ∅ := by
      simpa using hdis
    have htwo := (clebschPair G h r b).property
    rw [hempty] at htwo
    simp at htwo
  by_contra hnotadj
  have hcommon := h.of_not_adj hbcne hnotadj
  have hcommon' : #((G.commonNeighbors (b : V) (c : V)).toFinset) = 2 := by
    simpa [Set.toFinset_card] using hcommon
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < #((G.commonNeighbors
      (b : V) (c : V)).toFinset) by omega)
  have hxcommon : x ∈ G.commonNeighbors (b : V) (c : V) :=
    Set.mem_toFinset.mp hx
  have hbx : G.Adj (b : V) x := (G.mem_commonNeighbors.mp hxcommon).1
  have hcx : G.Adj (c : V) x := (G.mem_commonNeighbors.mp hxcommon).2
  have hbnotr : ¬G.Adj r (b : V) := (mem_clebschB G).mp b.property |>.2
  have hxne : x ≠ r := by
    intro hxr
    subst x
    exact hbnotr hbx.symm
  have hxnotr : ¬G.Adj r x := by
    intro hrx
    let a : ↥(clebschA G r) := ⟨x, (mem_clebschA G).mpr hrx⟩
    have hab : a ∈ (clebschPair G h r b : Finset ↥(clebschA G r)) :=
      (mem_clebschPair_iff G h r b a).mpr hbx
    have hac : a ∈ (clebschPair G h r c : Finset ↥(clebschA G r)) :=
      (mem_clebschPair_iff G h r c a).mpr hcx
    exact (Finset.disjoint_left.mp hdis hab) hac
  let d : ↥(clebschB G r) := ⟨x, (mem_clebschB G).mpr ⟨hxne, hxnotr⟩⟩
  let sb := (clebschPair G h r b : Finset ↥(clebschA G r))
  let sc := (clebschPair G h r c : Finset ↥(clebschA G r))
  let sd := (clebschPair G h r d : Finset ↥(clebschA G r))
  have hbd : G.Adj b d := by exact hbx
  have hcd : G.Adj c d := by exact hcx
  have hbd_dis : Disjoint sb sd := by
    exact clebschPair_disjoint_of_adj G h r b d hbd
  have hcd_dis : Disjoint sc sd := by
    exact clebschPair_disjoint_of_adj G h r c d hcd
  have hunion_dis : Disjoint (sb ∪ sc) sd := by
    rw [Finset.disjoint_left]
    intro a ha had
    rcases Finset.mem_union.mp ha with hab | hac
    · exact (Finset.disjoint_left.mp hbd_dis hab) had
    · exact (Finset.disjoint_left.mp hcd_dis hac) had
  have hlarge : #((sb ∪ sc) ∪ sd) = 6 := by
    rw [Finset.card_union_of_disjoint hunion_dis,
      Finset.card_union_of_disjoint hdis]
    dsimp [sb, sc, sd]
    rw [(clebschPair G h r b).property, (clebschPair G h r c).property,
      (clebschPair G h r d).property]
  have hsmall : #((sb ∪ sc) ∪ sd) ≤ 5 := by
    calc
      #((sb ∪ sc) ∪ sd) ≤ Fintype.card ↥(clebschA G r) :=
        Finset.card_le_univ _
      _ = 5 := by
        rw [Fintype.card_coe, card_clebschA G h r]
  omega

/-- In the `B` layer, adjacency is exactly disjointness of the two `A`-subsets. -/
theorem clebschPair_adj_iff_disjoint
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (b c : ↥(clebschB G r)) :
    G.Adj b c ↔
      Disjoint
        (clebschPair G h r b : Finset ↥(clebschA G r))
        (clebschPair G h r c : Finset ↥(clebschA G r)) := by
  exact ⟨clebschPair_disjoint_of_adj G h r b c,
    clebschPair_adj_of_disjoint G h r b c⟩

/-! ## The canonical root--point--pair model -/

/-- The pair layer over a finite point type. -/
abbrev ClebschTwoSubsets (A : Type*) [DecidableEq A] :=
  {s : Finset A // #s = 2}

/-- One root, the point layer, and the two-subset layer. -/
abbrev ClebschModelVertex (A : Type*) [DecidableEq A] :=
  Unit ⊕ (A ⊕ ClebschTwoSubsets A)

/-- Adjacency in the canonical Clebsch model: root--point, incidence between
points and pairs, and disjointness between pairs. -/
def clebschModelAdj {A : Type*} [DecidableEq A] :
    ClebschModelVertex A → ClebschModelVertex A → Prop
  | .inl _, .inr (.inl _) => True
  | .inr (.inl _), .inl _ => True
  | .inr (.inl a), .inr (.inr s) => a ∈ (s : Finset A)
  | .inr (.inr s), .inr (.inl a) => a ∈ (s : Finset A)
  | .inr (.inr s), .inr (.inr t) =>
      Disjoint (s : Finset A) (t : Finset A)
  | _, _ => False

/-- The canonical Clebsch graph on a five-point coordinate type. -/
def clebschModelGraph (A : Type*) [DecidableEq A] :
    SimpleGraph (ClebschModelVertex A) where
  Adj := clebschModelAdj
  symm := ⟨by
    intro x y hxy
    rcases x with (_ | a | s) <;> rcases y with (_ | b | t)
    all_goals simp_all [clebschModelAdj, disjoint_comm]⟩
  loopless := ⟨by
    intro x hxx
    rcases x with (_ | a | s)
    · exact hxx
    · exact hxx
    · exact (Finset.disjoint_self_iff_empty (s : Finset A)).mp hxx |>
        fun hs ↦ by simpa [hs] using s.property⟩

/-- Coordinate a vertex by the root, its point in `A`, or its pair in `B`. -/
noncomputable def clebschEncode
    (h : G.IsSRGWith 16 5 0 2) (r : V) (v : V) :
    ClebschModelVertex ↥(clebschA G r) :=
  if hvr : v = r then
    Sum.inl ()
  else if hva : v ∈ clebschA G r then
    Sum.inr (Sum.inl ⟨v, hva⟩)
  else
    Sum.inr (Sum.inr (clebschPairEquiv G h r
      ⟨v, (mem_clebschB G).mpr ⟨hvr, fun hadj ↦
        hva ((mem_clebschA G).mpr hadj)⟩⟩))

/-- Forget canonical coordinates and return to the original vertex set. -/
noncomputable def clebschDecode
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    ClebschModelVertex ↥(clebschA G r) → V
  | .inl _ => r
  | .inr (.inl a) => a
  | .inr (.inr s) => ((clebschPairEquiv G h r).symm s : ↥(clebschB G r))

@[simp] theorem clebschEncode_root
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    clebschEncode G h r r = Sum.inl () := by
  simp [clebschEncode]

@[simp] theorem clebschEncode_A
    (h : G.IsSRGWith 16 5 0 2) (r : V) (a : ↥(clebschA G r)) :
    clebschEncode G h r (a : V) = Sum.inr (Sum.inl a) := by
  have har : (a : V) ≠ r := by
    intro har
    exact root_not_mem_clebschA G r (by simpa [har] using a.property)
  simp [clebschEncode, har, a.property]

@[simp] theorem clebschEncode_B
    (h : G.IsSRGWith 16 5 0 2) (r : V) (b : ↥(clebschB G r)) :
    clebschEncode G h r (b : V) =
      Sum.inr (Sum.inr (clebschPairEquiv G h r b)) := by
  have hbr : (b : V) ≠ r := (mem_clebschB G).mp b.property |>.1
  have hbnot : ¬G.Adj r (b : V) := (mem_clebschB G).mp b.property |>.2
  have hbA : (b : V) ∉ clebschA G r := by
    intro hbA
    exact hbnot ((mem_clebschA G).mp hbA)
  simp [clebschEncode, hbr, hbA]

@[simp] theorem clebschDecode_root
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    clebschDecode G h r (Sum.inl ()) = r := rfl

@[simp] theorem clebschDecode_A
    (h : G.IsSRGWith 16 5 0 2) (r : V) (a : ↥(clebschA G r)) :
    clebschDecode G h r (Sum.inr (Sum.inl a)) = (a : V) := rfl

@[simp] theorem clebschDecode_pair
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (s : ClebschTwoSubsets ↥(clebschA G r)) :
    clebschDecode G h r (Sum.inr (Sum.inr s)) =
      (((clebschPairEquiv G h r).symm s : ↥(clebschB G r)) : V) := rfl

/-- The canonical root--point--pair coordinates form an equivalence. -/
noncomputable def clebschVertexEquiv
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    V ≃ ClebschModelVertex ↥(clebschA G r) where
  toFun := clebschEncode G h r
  invFun := clebschDecode G h r
  left_inv := by
    intro v
    by_cases hvr : v = r
    · subst v
      simp
    by_cases hva : v ∈ clebschA G r
    · let a : ↥(clebschA G r) := ⟨v, hva⟩
      rw [show clebschEncode G h r v = Sum.inr (Sum.inl a) by
        simpa [a] using clebschEncode_A G h r a]
      rfl
    · let b : ↥(clebschB G r) :=
        ⟨v, (mem_clebschB G).mpr ⟨hvr, fun hadj ↦
          hva ((mem_clebschA G).mpr hadj)⟩⟩
      rw [show clebschEncode G h r v =
          Sum.inr (Sum.inr (clebschPairEquiv G h r b)) by
        simpa [b] using clebschEncode_B G h r b]
      change (((clebschPairEquiv G h r).symm
        (clebschPairEquiv G h r b) : ↥(clebschB G r)) : V) = v
      exact congrArg Subtype.val ((clebschPairEquiv G h r).symm_apply_apply b)
  right_inv := by
    intro x
    rcases x with (_ | a | s)
    · change clebschEncode G h r r = Sum.inl ()
      exact clebschEncode_root G h r
    · change clebschEncode G h r (a : V) = Sum.inr (Sum.inl a)
      exact clebschEncode_A G h r a
    · let b : ↥(clebschB G r) := (clebschPairEquiv G h r).symm s
      rw [show clebschDecode G h r (Sum.inr (Sum.inr s)) = (b : V) by rfl]
      rw [clebschEncode_B G h r b]
      congr 2
      exact (clebschPairEquiv G h r).apply_symm_apply s

theorem clebschPair_equiv_symm
    (h : G.IsSRGWith 16 5 0 2) (r : V)
    (s : ClebschTwoSubsets ↥(clebschA G r)) :
    (clebschPair G h r ((clebschPairEquiv G h r).symm s) :
      Finset ↥(clebschA G r)) = (s : Finset ↥(clebschA G r)) := by
  exact congrArg Subtype.val ((clebschPairEquiv G h r).apply_symm_apply s)

/-- The canonical root--point--pair graph is isomorphic to every
`SRG(16,5,0,2)`.  This is the constructive uniqueness theorem. -/
noncomputable def clebschModelIsoTo
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    clebschModelGraph ↥(clebschA G r) ≃g G where
  toEquiv := (clebschVertexEquiv G h r).symm
  map_rel_iff' := by
    intro x y
    change G.Adj (clebschDecode G h r x) (clebschDecode G h r y) ↔
      clebschModelAdj x y
    rcases x with (_ | a | s) <;> rcases y with (_ | b | t)
    · simp [clebschModelAdj]
    · change G.Adj r (b : V) ↔ True
      simpa using (mem_clebschA G).mp b.property
    · let c : ↥(clebschB G r) := (clebschPairEquiv G h r).symm t
      change G.Adj r (c : V) ↔ False
      simp [((mem_clebschB G).mp c.property).2]
    · change G.Adj (a : V) r ↔ True
      simpa using ((mem_clebschA G).mp a.property).symm
    · change G.Adj (a : V) (b : V) ↔ False
      exact iff_false_intro (clebschA_pair_not_adj G h a.property b.property)
    · let c : ↥(clebschB G r) := (clebschPairEquiv G h r).symm t
      change G.Adj (a : V) (c : V) ↔ (a ∈ (t : Finset ↥(clebschA G r)))
      rw [← clebschPair_equiv_symm G h r t]
      simpa only [G.adj_comm] using (mem_clebschPair_iff G h r c a).symm
    · let c : ↥(clebschB G r) := (clebschPairEquiv G h r).symm s
      change G.Adj (c : V) r ↔ False
      rw [iff_false]
      simpa only [G.adj_comm] using ((mem_clebschB G).mp c.property).2
    · let c : ↥(clebschB G r) := (clebschPairEquiv G h r).symm s
      change G.Adj (c : V) (b : V) ↔ (b ∈ (s : Finset ↥(clebschA G r)))
      rw [← clebschPair_equiv_symm G h r s]
      exact (mem_clebschPair_iff G h r c b).symm
    · let c : ↥(clebschB G r) := (clebschPairEquiv G h r).symm s
      let d : ↥(clebschB G r) := (clebschPairEquiv G h r).symm t
      change G.Adj (c : V) (d : V) ↔
        Disjoint (s : Finset ↥(clebschA G r))
          (t : Finset ↥(clebschA G r))
      rw [← clebschPair_equiv_symm G h r s,
        ← clebschPair_equiv_symm G h r t]
      exact clebschPair_adj_iff_disjoint G h r c d

/-- Every `SRG(16,5,0,2)` is isomorphic to its canonical five-point
Clebsch model. -/
noncomputable def clebschUniqueIso
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    G ≃g clebschModelGraph ↥(clebschA G r) :=
  (clebschModelIsoTo G h r).symm

/-! ## Independence of the five-point coordinate type -/

/-- An equivalence of point types induces an equivalence of their
two-subset layers. -/
def clebschTwoSubsetsEquiv {A D : Type*} [DecidableEq A] [DecidableEq D]
    (e : A ≃ D) : ClebschTwoSubsets A ≃ ClebschTwoSubsets D :=
  Equiv.subtypeEquiv e.finsetCongr (fun s ↦ by simp)

@[simp] theorem clebschTwoSubsetsEquiv_val
    {A D : Type*} [DecidableEq A] [DecidableEq D]
    (e : A ≃ D) (s : ClebschTwoSubsets A) :
    ((clebschTwoSubsetsEquiv e s : ClebschTwoSubsets D) : Finset D) =
      (s : Finset A).map e.toEmbedding := rfl

/-- Relabeling the five points relabels the canonical Clebsch graph. -/
def clebschModelCongr {A D : Type*} [DecidableEq A] [DecidableEq D]
    (e : A ≃ D) : clebschModelGraph A ≃g clebschModelGraph D where
  toEquiv := Equiv.sumCongr (Equiv.refl Unit)
    (Equiv.sumCongr e (clebschTwoSubsetsEquiv e))
  map_rel_iff' := by
    intro x y
    rcases x with (_ | a | s) <;> rcases y with (_ | b | t)
    all_goals simp [clebschModelGraph, clebschModelAdj,
      clebschTwoSubsetsEquiv, Equiv.finsetCongr_apply]

end StronglyRegular

/-! ## Identification with the concrete critical template -/

/-- Concrete label of a two-subset of `Fin 5` in the untwisted `Fin 16`
Clebsch graph. Only the ten cardinality-two branches are reachable. -/
def clebschPairFin16Code (s : ClebschTwoSubsets (Fin 5)) : Fin 16 :=
  if (0 : Fin 5) ∈ (s : Finset (Fin 5)) then
    if (1 : Fin 5) ∈ (s : Finset (Fin 5)) then 9
    else if (2 : Fin 5) ∈ (s : Finset (Fin 5)) then 11
    else if (3 : Fin 5) ∈ (s : Finset (Fin 5)) then 13
    else 14
  else if (1 : Fin 5) ∈ (s : Finset (Fin 5)) then
    if (2 : Fin 5) ∈ (s : Finset (Fin 5)) then 2
    else if (3 : Fin 5) ∈ (s : Finset (Fin 5)) then 4
    else 7
  else if (2 : Fin 5) ∈ (s : Finset (Fin 5)) then
    if (3 : Fin 5) ∈ (s : Finset (Fin 5)) then 6
    else 5
  else 3

/-- Concrete labeling of root, point, and pair coordinates by `Fin 16`. -/
def clebschModelFin16Code : ClebschModelVertex (Fin 5) → Fin 16
  | .inl _ => 0
  | .inr (.inl a) => ![1, 8, 10, 12, 15] a
  | .inr (.inr s) => clebschPairFin16Code s

theorem clebschModelFin16Code_bijective :
    Function.Bijective clebschModelFin16Code := by
  decide

noncomputable def clebschModelFin16Equiv :
    ClebschModelVertex (Fin 5) ≃ Fin 16 :=
  Equiv.ofBijective clebschModelFin16Code clebschModelFin16Code_bijective

/-- Kernel-checked concrete bridge from the abstract five-point model to
color zero of the explicit untwisted critical template. -/
noncomputable def clebschModelFin16Iso :
    clebschModelGraph (Fin 5) ≃g colorGraph k16Untwisted (0 : ThreeColor) where
  toEquiv := clebschModelFin16Equiv
  map_rel_iff' := by
    intro x y
    change (colorGraph k16Untwisted (0 : ThreeColor)).Adj
      (clebschModelFin16Code x) (clebschModelFin16Code y) ↔
        clebschModelAdj x y
    rcases x with (⟨⟩ | a | s) <;> rcases y with (⟨⟩ | b | t)
    all_goals simp only [clebschModelFin16Code, clebschModelAdj, colorGraph]
    · decide
    · fin_cases b <;> decide
    · fin_cases t <;> decide
    · fin_cases a <;> decide
    · fin_cases a <;> fin_cases b <;> decide
    · fin_cases a <;> fin_cases t <;> decide
    · fin_cases s <;> decide
    · fin_cases s <;> fin_cases b <;> decide
    · fin_cases s <;> fin_cases t <;> decide

/-- Choose coordinates for the five neighbours of the root. -/
noncomputable def clebschPointsEquivFin5
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    ↥(clebschA G r) ≃ Fin 5 :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_coe, card_clebschA G h r]
    decide)

/-- Concrete uniqueness: every `SRG(16,5,0,2)` is graph-isomorphic to
color zero of `k16Untwisted` from `CriticalTemplates`. -/
noncomputable def clebschIsoK16Untwisted
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.IsSRGWith 16 5 0 2) (r : V) :
    G ≃g colorGraph k16Untwisted (0 : ThreeColor) :=
  (clebschUniqueIso G h r).trans
    ((clebschModelCongr (clebschPointsEquivFin5 G h r)).trans
      clebschModelFin16Iso)

#print axioms R4333.clebschModelFin16Code_bijective
#print axioms R4333.clebschModelFin16Iso
#print axioms R4333.clebschIsoK16Untwisted

end R4333
