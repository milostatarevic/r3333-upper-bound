import R4333Lean.CriticalTemplateMaximumSetIntersection
import R4333Lean.CriticalK15ColorPreservingClassification

/-!
# Exact labelled three-colour partitions of the critical K15 templates

A labelled partition is encoded by a word `Fin 15 → Fin 3`; the value at a
vertex records whether it belongs to part zero, one, or two.  The finite
checker below asks that every part have five vertices and that part `q`
contain no edge of template colour `q`.

Ordinary kernel reduction proves that each of the two fixed critical K15
templates has exactly one such labelled word.  No solver output, axiom, or
unverified enumeration is used.
-/

namespace R4333
namespace CriticalK15PartitionClassification

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev PartitionWord := Fin 15 → Fin 3

/-- The vertices carrying one label in an encoded partition. -/
def part (word : PartitionWord) (q : Fin 3) : Finset (Fin 15) :=
  Finset.univ.filter fun vertex => word vertex = q

/-- Computable form: all three labelled parts have order five, and the
ordered-pair violation count for part `q` in template colour `q` is zero. -/
def IsTemplatePartition (twisted : Bool) (word : PartitionWord) : Prop :=
  ∀ q : Fin 3,
    (part word q).card = 5 ∧
      colorViolationCount (k15Template twisted) q (part word q) = 0

/-- The computable word predicate has exactly the intended semantic meaning. -/
theorem isTemplatePartition_iff (twisted : Bool) (word : PartitionWord) :
    IsTemplatePartition twisted word ↔
      ∀ q : Fin 3,
        (part word q).card = 5 ∧
          IsColorIndependentSet (k15Template twisted) q (part word q) := by
  constructor
  · intro h q
    exact ⟨(h q).1,
      (colorViolationCount_eq_zero_iff _ _ _).mp (h q).2⟩
  · intro h q
    exact ⟨(h q).1,
      (colorViolationCount_eq_zero_iff _ _ _).mpr (h q).2⟩

/-- Unique untwisted partition word. -/
def untwistedPartitionWord : PartitionWord :=
  ![0, 2, 1, 0, 1, 0, 2, 0, 1, 2, 2, 2, 1, 1, 0]

/-- Unique twisted partition word. -/
def twistedPartitionWord : PartitionWord :=
  ![0, 1, 2, 0, 1, 0, 2, 0, 2, 2, 2, 1, 1, 1, 0]

def untwistedPartZero : Finset (Fin 15) := {0, 3, 5, 7, 14}
def untwistedPartOne : Finset (Fin 15) := {2, 4, 8, 12, 13}
def untwistedPartTwo : Finset (Fin 15) := {1, 6, 9, 10, 11}

def twistedPartZero : Finset (Fin 15) := {0, 3, 5, 7, 14}
def twistedPartOne : Finset (Fin 15) := {1, 4, 11, 12, 13}
def twistedPartTwo : Finset (Fin 15) := {2, 6, 8, 9, 10}

theorem untwistedPartitionWord_parts :
    part untwistedPartitionWord 0 = untwistedPartZero ∧
    part untwistedPartitionWord 1 = untwistedPartOne ∧
    part untwistedPartitionWord 2 = untwistedPartTwo := by
  decide

theorem twistedPartitionWord_parts :
    part twistedPartitionWord 0 = twistedPartZero ∧
    part twistedPartitionWord 1 = twistedPartOne ∧
    part twistedPartitionWord 2 = twistedPartTwo := by
  decide

theorem untwistedPartitionWord_valid :
    IsTemplatePartition false untwistedPartitionWord := by
  unfold IsTemplatePartition
  decide

theorem twistedPartitionWord_valid :
    IsTemplatePartition true twistedPartitionWord := by
  unfold IsTemplatePartition
  decide

/-! ## A compact staged exhaustive check -/

/-- The `3003` five-subsets of the labelled vertex set. -/
def fiveSubsets : Finset (Finset (Fin 15)) :=
  (Finset.univ : Finset (Fin 15)).powersetCard 5

/-- Candidate five-sets for one selected template colour. -/
def independentFiveSets (twisted : Bool) (q : Fin 3) :
    Finset (Finset (Fin 15)) :=
  fiveSubsets.filter fun S =>
    colorViolationCount (k15Template twisted) q S = 0

abbrev IndependentFiveSet (twisted : Bool) (q : Fin 3) :=
  {S : Finset (Fin 15) // S ∈ independentFiveSets twisted q}

theorem mem_independentFiveSets_iff
    (twisted : Bool) (q : Fin 3) (S : Finset (Fin 15)) :
    S ∈ independentFiveSets twisted q ↔
      S.card = 5 ∧ IsColorIndependentSet (k15Template twisted) q S := by
  simp [independentFiveSets, fiveSubsets,
    colorViolationCount_eq_zero_iff]

/-- Kernel enumeration after filtering to maximum independent sets.  This is
equivalent to checking all partition words, but avoids repeatedly examining
the overwhelmingly many words that already fail one colour class. -/
theorem untwisted_candidate_triple_unique :
    ∀ (A : IndependentFiveSet false 0)
      (B : IndependentFiveSet false 1)
      (C : IndependentFiveSet false 2),
      Disjoint A.1 B.1 → Disjoint A.1 C.1 → Disjoint B.1 C.1 →
      (A.1 ∪ B.1) ∪ C.1 = Finset.univ →
      A.1 = untwistedPartZero ∧
        B.1 = untwistedPartOne ∧ C.1 = untwistedPartTwo := by
  unfold IndependentFiveSet independentFiveSets fiveSubsets
  decide

theorem twisted_candidate_triple_unique :
    ∀ (A : IndependentFiveSet true 0)
      (B : IndependentFiveSet true 1)
      (C : IndependentFiveSet true 2),
      Disjoint A.1 B.1 → Disjoint A.1 C.1 → Disjoint B.1 C.1 →
      (A.1 ∪ B.1) ∪ C.1 = Finset.univ →
      A.1 = twistedPartZero ∧
        B.1 = twistedPartOne ∧ C.1 = twistedPartTwo := by
  unfold IndependentFiveSet independentFiveSets fiveSubsets
  decide

/-! ## Semantic uniqueness -/

theorem untwisted_partition_unique
    (A B C : Finset (Fin 15))
    (hAcard : A.card = 5) (hBcard : B.card = 5) (hCcard : C.card = 5)
    (hA : IsColorIndependentSet (k15Template false) 0 A)
    (hB : IsColorIndependentSet (k15Template false) 1 B)
    (hC : IsColorIndependentSet (k15Template false) 2 C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : (A ∪ B) ∪ C = Finset.univ) :
    A = untwistedPartZero ∧
      B = untwistedPartOne ∧ C = untwistedPartTwo := by
  let candidateA : IndependentFiveSet false 0 :=
    ⟨A, (mem_independentFiveSets_iff false 0 A).2 ⟨hAcard, hA⟩⟩
  let candidateB : IndependentFiveSet false 1 :=
    ⟨B, (mem_independentFiveSets_iff false 1 B).2 ⟨hBcard, hB⟩⟩
  let candidateC : IndependentFiveSet false 2 :=
    ⟨C, (mem_independentFiveSets_iff false 2 C).2 ⟨hCcard, hC⟩⟩
  simpa [candidateA, candidateB, candidateC] using
    untwisted_candidate_triple_unique candidateA candidateB candidateC
      hAB hAC hBC hcover

theorem twisted_partition_unique
    (A B C : Finset (Fin 15))
    (hAcard : A.card = 5) (hBcard : B.card = 5) (hCcard : C.card = 5)
    (hA : IsColorIndependentSet (k15Template true) 0 A)
    (hB : IsColorIndependentSet (k15Template true) 1 B)
    (hC : IsColorIndependentSet (k15Template true) 2 C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : (A ∪ B) ∪ C = Finset.univ) :
    A = twistedPartZero ∧
      B = twistedPartOne ∧ C = twistedPartTwo := by
  let candidateA : IndependentFiveSet true 0 :=
    ⟨A, (mem_independentFiveSets_iff true 0 A).2 ⟨hAcard, hA⟩⟩
  let candidateB : IndependentFiveSet true 1 :=
    ⟨B, (mem_independentFiveSets_iff true 1 B).2 ⟨hBcard, hB⟩⟩
  let candidateC : IndependentFiveSet true 2 :=
    ⟨C, (mem_independentFiveSets_iff true 2 C).2 ⟨hCcard, hC⟩⟩
  simpa [candidateA, candidateB, candidateC] using
    twisted_candidate_triple_unique candidateA candidateB candidateC
      hAB hAC hBC hcover

def canonicalPart (twisted : Bool) : Fin 3 → Finset (Fin 15) :=
  if twisted then ![twistedPartZero, twistedPartOne, twistedPartTwo]
  else ![untwistedPartZero, untwistedPartOne, untwistedPartTwo]

theorem template_partition_unique
    (twisted : Bool) (A B C : Finset (Fin 15))
    (hAcard : A.card = 5) (hBcard : B.card = 5) (hCcard : C.card = 5)
    (hA : IsColorIndependentSet (k15Template twisted) 0 A)
    (hB : IsColorIndependentSet (k15Template twisted) 1 B)
    (hC : IsColorIndependentSet (k15Template twisted) 2 C)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : (A ∪ B) ∪ C = Finset.univ) :
    A = canonicalPart twisted 0 ∧
      B = canonicalPart twisted 1 ∧ C = canonicalPart twisted 2 := by
  cases twisted with
  | false =>
      simpa [canonicalPart] using untwisted_partition_unique A B C
        hAcard hBcard hCcard hA hB hC hAB hAC hBC hcover
  | true =>
      simpa [canonicalPart] using twisted_partition_unique A B C
        hAcard hBcard hCcard hA hB hC hAB hAC hBC hcover

/-! ## Recovering uniqueness of the compact word -/

theorem part_disjoint (word : PartitionWord) {q r : Fin 3} (hqr : q ≠ r) :
    Disjoint (part word q) (part word r) := by
  rw [Finset.disjoint_left]
  intro vertex hq hr
  simp only [part, Finset.mem_filter, Finset.mem_univ, true_and] at hq hr
  exact hqr (hq.symm.trans hr)

theorem parts_cover (word : PartitionWord) :
    (part word 0 ∪ part word 1) ∪ part word 2 = Finset.univ := by
  ext vertex
  simp only [part, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
    true_and, iff_true]
  generalize hq : word vertex = q
  fin_cases q <;> simp

theorem partitionWord_ext {left right : PartitionWord}
    (hparts : ∀ q : Fin 3, part left q = part right q) : left = right := by
  funext vertex
  have hmem : vertex ∈ part left (left vertex) := by simp [part]
  rw [hparts (left vertex)] at hmem
  have hvalue : right vertex = left vertex := by simpa [part] using hmem
  exact hvalue.symm

theorem untwistedPartitionWord_unique (word : PartitionWord)
    (hword : IsTemplatePartition false word) :
    word = untwistedPartitionWord := by
  have hsemantic := (isTemplatePartition_iff false word).mp hword
  have hclassified := untwisted_partition_unique
    (part word 0) (part word 1) (part word 2)
    (hsemantic 0).1 (hsemantic 1).1 (hsemantic 2).1
    (hsemantic 0).2 (hsemantic 1).2 (hsemantic 2).2
    (part_disjoint word (by decide))
    (part_disjoint word (by decide))
    (part_disjoint word (by decide)) (parts_cover word)
  apply partitionWord_ext
  intro q
  fin_cases q
  · exact hclassified.1.trans untwistedPartitionWord_parts.1.symm
  · exact hclassified.2.1.trans untwistedPartitionWord_parts.2.1.symm
  · exact hclassified.2.2.trans untwistedPartitionWord_parts.2.2.symm

theorem twistedPartitionWord_unique (word : PartitionWord)
    (hword : IsTemplatePartition true word) :
    word = twistedPartitionWord := by
  have hsemantic := (isTemplatePartition_iff true word).mp hword
  have hclassified := twisted_partition_unique
    (part word 0) (part word 1) (part word 2)
    (hsemantic 0).1 (hsemantic 1).1 (hsemantic 2).1
    (hsemantic 0).2 (hsemantic 1).2 (hsemantic 2).2
    (part_disjoint word (by decide))
    (part_disjoint word (by decide))
    (part_disjoint word (by decide)) (parts_cover word)
  apply partitionWord_ext
  intro q
  fin_cases q
  · exact hclassified.1.trans twistedPartitionWord_parts.1.symm
  · exact hclassified.2.1.trans twistedPartitionWord_parts.2.1.symm
  · exact hclassified.2.2.trans twistedPartitionWord_parts.2.2.symm

/-! ## Transport through an arbitrary weak colour equivalence -/

namespace WeakColorEquiv

/-- A partition in any weakly equivalent colouring becomes the unique
canonical labelled partition after applying the equivalence's vertex map.
The three source colours are the inverse images of template labels
`0`, `1`, and `2`, so global palette relabeling is handled explicitly. -/
theorem partition_images_eq_canonical
    {V Color : Type*} [Fintype V] [DecidableEq V]
    [Fintype Color] [DecidableEq Color]
    {c : EdgeColoring V Color} (twisted : Bool)
    (e : WeakColorEquiv c (k15Template twisted))
    (A B D : Finset V)
    (hAcard : A.card = 5) (hBcard : B.card = 5) (hDcard : D.card = 5)
    (hA : IsColorIndependentSet c (e.colors.symm 0) A)
    (hB : IsColorIndependentSet c (e.colors.symm 1) B)
    (hD : IsColorIndependentSet c (e.colors.symm 2) D)
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    (hcover : (A ∪ B) ∪ D = Finset.univ) :
    A.image e.vertex = canonicalPart twisted 0 ∧
      B.image e.vertex = canonicalPart twisted 1 ∧
      D.image e.vertex = canonicalPart twisted 2 := by
  apply template_partition_unique twisted
  · exact (Finset.card_image_of_injective A e.vertex.injective).trans hAcard
  · exact (Finset.card_image_of_injective B e.vertex.injective).trans hBcard
  · exact (Finset.card_image_of_injective D e.vertex.injective).trans hDcard
  · simpa using e.image_isColorIndependentSet (e.colors.symm 0) A hA
  · simpa using e.image_isColorIndependentSet (e.colors.symm 1) B hB
  · simpa using e.image_isColorIndependentSet (e.colors.symm 2) D hD
  · exact (Finset.disjoint_image e.vertex.injective).2 hAB
  · exact (Finset.disjoint_image e.vertex.injective).2 hAD
  · exact (Finset.disjoint_image e.vertex.injective).2 hBD
  · have himage :
        ((A ∪ B) ∪ D).image e.vertex =
          (Finset.univ : Finset V).image e.vertex :=
      congrArg (fun S : Finset V => S.image e.vertex) hcover
    simpa only [Finset.image_union, Finset.image_univ_equiv] using himage

end WeakColorEquiv

/-- Every good labelled K15 colouring admits a colour-preserving weak
equivalence to one of the two templates.  This repackages the existing
colour-preserving classification in the interface used by the transport
theorem above. -/
theorem exists_colorPreservingWeakEquiv_to_k15Template
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ twisted : Bool,
      ∃ e : WeakColorEquiv c (k15Template twisted),
        e.colors = Equiv.refl ThreeColor := by
  obtain ⟨twisted, vertex, hnormalize⟩ :=
    exists_colorPreserving_k15Template c hc
  let e : WeakColorEquiv c (k15Template twisted) := {
    vertex := vertex.symm
    colors := Equiv.refl ThreeColor
    map_color := by
      intro left right hlr
      simpa using hnormalize (vertex.symm left) (vertex.symm right)
        (vertex.symm.injective.ne hlr)
  }
  exact ⟨twisted, e, rfl⟩

/-- Fully transported form for an arbitrary good labelled K15 colouring.
One colour-preserving normalization simultaneously sends every labelled
`(5,5,5)` independent partition to the appropriate unique canonical triple. -/
theorem exists_partition_normalization_of_good
    (c : EdgeColoring (Fin 15) ThreeColor)
    (hc : NoMonochromaticTriangle c) :
    ∃ twisted : Bool,
      ∃ e : WeakColorEquiv c (k15Template twisted),
        e.colors = Equiv.refl ThreeColor ∧
        ∀ A B D : Finset (Fin 15),
          A.card = 5 → B.card = 5 → D.card = 5 →
          IsColorIndependentSet c 0 A →
          IsColorIndependentSet c 1 B →
          IsColorIndependentSet c 2 D →
          Disjoint A B → Disjoint A D → Disjoint B D →
          (A ∪ B) ∪ D = Finset.univ →
          A.image e.vertex = canonicalPart twisted 0 ∧
            B.image e.vertex = canonicalPart twisted 1 ∧
            D.image e.vertex = canonicalPart twisted 2 := by
  obtain ⟨twisted, e, he⟩ :=
    exists_colorPreservingWeakEquiv_to_k15Template c hc
  refine ⟨twisted, e, he, ?_⟩
  intro A B D hAcard hBcard hDcard hA hB hD hAB hAD hBD hcover
  apply WeakColorEquiv.partition_images_eq_canonical twisted e A B D
    hAcard hBcard hDcard
  · simpa [he] using hA
  · simpa [he] using hB
  · simpa [he] using hD
  · exact hAB
  · exact hAD
  · exact hBD
  · exact hcover

#print axioms R4333.CriticalK15PartitionClassification.untwisted_candidate_triple_unique
#print axioms R4333.CriticalK15PartitionClassification.twisted_candidate_triple_unique
#print axioms R4333.CriticalK15PartitionClassification.untwisted_partition_unique
#print axioms R4333.CriticalK15PartitionClassification.twisted_partition_unique
#print axioms R4333.CriticalK15PartitionClassification.untwistedPartitionWord_unique
#print axioms R4333.CriticalK15PartitionClassification.twistedPartitionWord_unique
#print axioms R4333.CriticalK15PartitionClassification.WeakColorEquiv.partition_images_eq_canonical
#print axioms R4333.CriticalK15PartitionClassification.exists_colorPreservingWeakEquiv_to_k15Template
#print axioms R4333.CriticalK15PartitionClassification.exists_partition_normalization_of_good

end CriticalK15PartitionClassification
end R4333
