import R4333Lean.ClebschCompletionSemantics
import R4333Lean.CriticalTemplates

/-!
# Classification of the 72 canonical Clebsch completions

The explicit rows and vertex maps are finite data.  Their correctness is
checked again below by kernel reduction; the external canonical-labeling
program is not trusted.
-/

namespace R4333

private theorem fin3_cases_completion (q : ThreeColor) :
    q = 0 ∨ q = 1 ∨ q = 2 := by
  fin_cases q <;> simp

/-- The `i`th one of the seventy-two explicit completion rows. -/
def clebschDecompositionAt (i : Fin 72) : List Bool :=
  clebschDecompositions.getD i []

/-- `false` selects the untwisted template and `true` the twisted one. -/
def clebschCompletionTargetAt (i : Fin 72) : Bool :=
  clebschCompletionTargets.getD i false

/-- Explicit vertex map from completion `i` to its selected template. -/
def clebschCompletionTemplateMapAt (i : Fin 72) : Fin 16 → Fin 16 :=
  clebschCompletionTemplateMaps.getD i id

theorem clebschDecompositions_length : clebschDecompositions.length = 72 := by
  decide

theorem clebschCompletionTargets_length : clebschCompletionTargets.length = 72 := by
  decide

theorem clebschCompletionTemplateMaps_length :
    clebschCompletionTemplateMaps.length = 72 := by
  decide

/-- Every listed row has an actual `Fin 72` index. -/
theorem exists_clebschDecompositionAt_of_mem {bits : List Bool}
    (hbits : bits ∈ clebschDecompositions) :
    ∃ i : Fin 72, clebschDecompositionAt i = bits := by
  let j := clebschDecompositions.idxOf bits
  have hj : j < clebschDecompositions.length :=
    List.idxOf_lt_length_iff.mpr hbits
  let i : Fin 72 := ⟨j, by simpa [clebschDecompositions_length] using hj⟩
  refine ⟨i, ?_⟩
  simp only [clebschDecompositionAt, i, j]
  rw [List.getD_eq_getElem?_getD, List.getElem?_idxOf hbits]
  rfl

/-- Rebuild a canonical three-colouring from one Boolean completion row. -/
def canonicalClebschCompletion (bits : List Bool) :
    EdgeColoring (Fin 16) ThreeColor where
  color u v :=
    if u = v then 0
    else if canonicalClebschRed u.val v.val then 0
    else if bits.getD (clebschComplementIndex u.val v.val) false then 1 else 2
  color_symm u v := by
    have hred : canonicalClebschRed u.val v.val =
        canonicalClebschRed v.val u.val := by
      simp [canonicalClebschRed, canonicalPairCode, min_comm, max_comm]
    have hindex : clebschComplementIndex u.val v.val =
        clebschComplementIndex v.val u.val := by
      simp [clebschComplementIndex, min_comm, max_comm]
    by_cases h : u = v
    · subst v
      rfl
    · have h' : v ≠ u := Ne.symm h
      simp only [h, h', ↓reduceIte]
      rw [hred, hindex]

theorem canonicalClebschCompletion_zero_iff
    (bits : List Bool) (u v : Fin 16) (huv : u ≠ v) :
    canonicalClebschCompletion bits u v = (0 : ThreeColor) ↔
      canonicalClebschRed u.val v.val = true := by
  change (if u = v then 0
    else if canonicalClebschRed u.val v.val = true then 0
    else if bits.getD (clebschComplementIndex u.val v.val) false = true then 1 else 2) = 0 ↔ _
  cases hred : canonicalClebschRed u.val v.val
  · simp only [huv, Bool.false_eq_true, if_false]
    split <;> decide
  · simp [huv]

/-- The simple graph represented by the fixed canonical zero colour. -/
def canonicalClebschGraph : SimpleGraph (Fin 16) where
  Adj u v := u ≠ v ∧ canonicalClebschRed u.val v.val = true
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm, ?_⟩
    simpa [canonicalClebschRed, canonicalPairCode, min_comm, max_comm] using h.2⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem canonicalClebschGraph_adj_iff (bits : List Bool) (u v : Fin 16) :
    canonicalClebschGraph.Adj u v ↔
      (colorGraph (canonicalClebschCompletion bits) (0 : ThreeColor)).Adj u v := by
  change (u ≠ v ∧ canonicalClebschRed u.val v.val = true) ↔
    (u ≠ v ∧ canonicalClebschCompletion bits u v = (0 : ThreeColor))
  constructor
  · rintro ⟨huv, hred⟩
    exact ⟨huv, (canonicalClebschCompletion_zero_iff bits u v huv).mpr hred⟩
  · rintro ⟨huv, hzero⟩
    exact ⟨huv, (canonicalClebschCompletion_zero_iff bits u v huv).mp hzero⟩

/-- A canonical colouring is determined, away from the diagonal, by its
eighty-bit completion vector. -/
theorem eq_canonicalClebschCompletion_of_bits
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hcanonical : HasCanonicalClebschZero d)
    (bits : List Bool)
    (hbits : clebschCompletionBits d = bits) :
    ∀ u v, u ≠ v → d u v = canonicalClebschCompletion bits u v := by
  intro u v huv
  wlog huvlt : u.val < v.val generalizing u v
  · have hvult : v.val < u.val := by
      have hneval : u.val ≠ v.val := fun h => huv (Fin.ext h)
      omega
    rw [d.color_symm u v, (canonicalClebschCompletion bits).color_symm u v]
    exact this v u huv.symm hvult
  have hredCases : canonicalClebschRed u.val v.val = true ∨
      canonicalClebschRed u.val v.val = false := by
    cases h : canonicalClebschRed u.val v.val <;> simp_all
  rcases hredCases with hred | hred
  · have hzero := (hcanonical u v huv).mpr hred
    change d u v =
      (if u = v then 0 else if canonicalClebschRed u.val v.val = true then 0
       else if bits.getD (clebschComplementIndex u.val v.val) false = true then 1 else 2)
    simp [huv, hred, hzero]
  · have hval := clebschCompletionValuation_edge d
      u.isLt v.isLt huvlt hred
    change ((clebschCompletionBits d).getD
      (clebschComplementIndex u.val v.val) false = true ↔
        d u v = (1 : ThreeColor)) at hval
    rw [hbits] at hval
    have hn0 : d u v ≠ (0 : ThreeColor) := by
      intro hzero
      have := (hcanonical u v huv).mp hzero
      simp [hred] at this
    by_cases hone : d u v = (1 : ThreeColor)
    · have hbit := hval.mpr hone
      have hbit' : bits[clebschComplementIndex u.val v.val]?.getD false = true := by
        simpa only [List.getD_eq_getElem?_getD] using hbit
      change d u v =
        (if u = v then 0 else if canonicalClebschRed u.val v.val = true then 0
         else if bits.getD (clebschComplementIndex u.val v.val) false = true then 1 else 2)
      simp [huv, hred, hbit', hone]
    · have hbit : bits.getD (clebschComplementIndex u.val v.val) false = false := by
        cases h : bits.getD (clebschComplementIndex u.val v.val) false <;>
          simp_all
      have htwo : d u v = (2 : ThreeColor) := by
        rcases fin3_cases_completion (d u v) with h | h | h <;> simp_all
      have hbit' : bits[clebschComplementIndex u.val v.val]?.getD false = false := by
        simpa only [List.getD_eq_getElem?_getD] using hbit
      change d u v =
        (if u = v then 0 else if canonicalClebschRed u.val v.val = true then 0
         else if bits.getD (clebschComplementIndex u.val v.val) false = true then 1 else 2)
      simp [huv, hred, hbit', htwo]

/-- The critical template selected by the finite classification row. -/
def clebschSelectedTemplate (i : Fin 72) :
    EdgeColoring (Fin 16) ThreeColor :=
  if clebschCompletionTargetAt i then k16Twisted else k16Untwisted

set_option maxRecDepth 100000 in
theorem clebschCompletionTemplateMapAt_bijective (i : Fin 72) :
    Function.Bijective (clebschCompletionTemplateMapAt i) := by
  fin_cases i <;> decide

/-- Promote each checked explicit permutation to a genuine equivalence. -/
noncomputable def clebschCompletionTemplateEquiv (i : Fin 72) : Fin 16 ≃ Fin 16 :=
  Equiv.ofBijective (clebschCompletionTemplateMapAt i)
    (clebschCompletionTemplateMapAt_bijective i)

@[simp] theorem clebschCompletionTemplateEquiv_apply (i : Fin 72) (u : Fin 16) :
    clebschCompletionTemplateEquiv i u = clebschCompletionTemplateMapAt i u := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of all 72 direct maps, across every off-diagonal
edge. -/
theorem clebschCompletionTemplateMap_correct (i : Fin 72) :
    ∀ u v, u ≠ v →
      canonicalClebschCompletion (clebschDecompositionAt i) u v =
        clebschSelectedTemplate i
          (clebschCompletionTemplateMapAt i u)
          (clebschCompletionTemplateMapAt i v) := by
  fin_cases i <;> decide

theorem clebschSelectedTemplate_zero :
    clebschSelectedTemplate (0 : Fin 72) = k16Untwisted := by
  have htarget : clebschCompletionTargetAt (0 : Fin 72) = false := by decide
  simp [clebschSelectedTemplate, htarget]

/-- The explicit row-zero map identifies the certificate's canonical
Clebsch labels with the algebraic labels used by `k16Untwisted`. -/
noncomputable def canonicalClebschIsoUntwisted :
    canonicalClebschGraph ≃g colorGraph k16Untwisted (0 : ThreeColor) where
  toEquiv := clebschCompletionTemplateEquiv 0
  map_rel_iff' := by
    intro u v
    constructor
    · intro htarget
      have hmapne : clebschCompletionTemplateMapAt 0 u ≠
          clebschCompletionTemplateMapAt 0 v := htarget.1
      have huv : u ≠ v := fun huv => hmapne (congrArg _ huv)
      have hcolor := clebschCompletionTemplateMap_correct 0 u v huv
      rw [clebschSelectedTemplate_zero] at hcolor
      have hzero : canonicalClebschCompletion (clebschDecompositionAt 0) u v = 0 :=
        hcolor.trans htarget.2
      exact ⟨huv,
        (canonicalClebschCompletion_zero_iff _ u v huv).mp hzero⟩
    · rintro ⟨huv, hred⟩
      have hcolor := clebschCompletionTemplateMap_correct 0 u v huv
      rw [clebschSelectedTemplate_zero] at hcolor
      refine ⟨(clebschCompletionTemplateEquiv 0).injective.ne huv, ?_⟩
      change k16Untwisted
          (clebschCompletionTemplateMapAt 0 u)
          (clebschCompletionTemplateMapAt 0 v) = 0
      rw [← hcolor]
      exact (canonicalClebschCompletion_zero_iff _ u v huv).mpr hred

/-- Each one of the 72 rows is explicitly weakly isomorphic to one of the
two critical templates. -/
noncomputable def canonicalCompletionWeakEquiv (i : Fin 72) :
    WeakColorEquiv (canonicalClebschCompletion (clebschDecompositionAt i))
      (clebschSelectedTemplate i) where
  vertex := clebschCompletionTemplateEquiv i
  colors := Equiv.refl ThreeColor
  map_color := by
    intro u v huv
    simpa using clebschCompletionTemplateMap_correct i u v huv

/-- End-to-end classification once the zero graph has been normalized to
the canonical Clebsch labels. -/
theorem canonicalClebschZero_classified
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d)
    (hcanonical : HasCanonicalClebschZero d) :
    ∃ t ∈ k16CriticalCatalogue, Nonempty (WeakColorEquiv d t) := by
  have hmem := clebschCompletionBits_mem d hd hcanonical
  obtain ⟨i, hi⟩ := exists_clebschDecompositionAt_of_mem hmem
  let e : WeakColorEquiv d (clebschSelectedTemplate i) := {
    vertex := clebschCompletionTemplateEquiv i
    colors := Equiv.refl ThreeColor
    map_color := by
      intro u v huv
      calc
        d u v = canonicalClebschCompletion (clebschCompletionBits d) u v :=
          eq_canonicalClebschCompletion_of_bits d hcanonical
            (clebschCompletionBits d) rfl u v huv
        _ = canonicalClebschCompletion (clebschDecompositionAt i) u v := by
          rw [hi]
        _ = clebschSelectedTemplate i
              (clebschCompletionTemplateMapAt i u)
              (clebschCompletionTemplateMapAt i v) :=
          clebschCompletionTemplateMap_correct i u v huv
        _ = clebschSelectedTemplate i
              (clebschCompletionTemplateEquiv i u)
              (clebschCompletionTemplateEquiv i v) := by rfl
  }
  refine ⟨clebschSelectedTemplate i, ?_, ⟨e⟩⟩
  by_cases htarget : clebschCompletionTargetAt i = true
  · simp [k16CriticalCatalogue, clebschSelectedTemplate, htarget]
  · have hfalse : clebschCompletionTargetAt i = false := by
      cases h : clebschCompletionTargetAt i <;> simp_all
    simp [k16CriticalCatalogue, clebschSelectedTemplate, hfalse]

/-- Any good colouring whose zero-colour graph is graph-isomorphic to the
canonical Clebsch graph is one of the two critical colourings.  The graph
isomorphism is used only to relabel vertices; the other two colours remain
fully visible to the checked 72-row exhaustion. -/
theorem classified_of_zeroGraph_iso_canonical
    (d : EdgeColoring (Fin 16) ThreeColor)
    (hd : NoMonochromaticTriangle d)
    (g : colorGraph d (0 : ThreeColor) ≃g canonicalClebschGraph) :
    ∃ t ∈ k16CriticalCatalogue, Nonempty (WeakColorEquiv d t) := by
  let dcanonical : EdgeColoring (Fin 16) ThreeColor :=
    relabelVertices d g.symm.toEquiv
  have hdcanonical : NoMonochromaticTriangle dcanonical :=
    noMono_relabelVertices d g.symm.toEquiv hd
  have hcanonical : HasCanonicalClebschZero dcanonical := by
    intro a b hab
    have hpreNe : g.symm a ≠ g.symm b := g.symm.injective.ne hab
    have hmap := g.map_rel_iff (a := g.symm a) (b := g.symm b)
    have hga : g (g.symm a) = a := g.toEquiv.apply_symm_apply a
    have hgb : g (g.symm b) = b := g.toEquiv.apply_symm_apply b
    change d (g.symm a) (g.symm b) = (0 : ThreeColor) ↔
      canonicalClebschRed a.val b.val = true
    constructor
    · intro hzero
      have hsource : (colorGraph d (0 : ThreeColor)).Adj (g.symm a) (g.symm b) :=
        ⟨hpreNe, hzero⟩
      have htarget : canonicalClebschGraph.Adj (g (g.symm a)) (g (g.symm b)) :=
        hmap.symm.mp hsource
      rw [hga, hgb] at htarget
      exact htarget.2
    · intro hred
      have htarget : canonicalClebschGraph.Adj (g (g.symm a)) (g (g.symm b)) := by
        rw [hga, hgb]
        exact ⟨hab, hred⟩
      have hsource : (colorGraph d (0 : ThreeColor)).Adj (g.symm a) (g.symm b) :=
        hmap.mp htarget
      exact hsource.2
  obtain ⟨t, ht, ⟨f⟩⟩ :=
    canonicalClebschZero_classified dcanonical hdcanonical hcanonical
  let toCanonical : WeakColorEquiv d dcanonical := {
    vertex := g.toEquiv
    colors := Equiv.refl ThreeColor
    map_color := by
      intro u v huv
      change d u v = d (g.symm (g u)) (g.symm (g v))
      simp
  }
  exact ⟨t, ht, ⟨toCanonical.trans f⟩⟩

#print axioms R4333.eq_canonicalClebschCompletion_of_bits
#print axioms R4333.clebschCompletionTemplateMap_correct
#print axioms R4333.canonicalClebschIsoUntwisted
#print axioms R4333.canonicalClebschZero_classified
#print axioms R4333.classified_of_zeroGraph_iso_canonical

end R4333
