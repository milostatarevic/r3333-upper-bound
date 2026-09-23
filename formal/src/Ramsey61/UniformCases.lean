import Ramsey61.DenseBipartite
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace Ramsey61
open Finset SimpleGraph

namespace UniformCases

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Positive minimum degree makes the bipartition cover every actual vertex. -/
theorem exists_ordered_parts (G : SimpleGraph V) [DecidableRel G.Adj]
    [Nonempty V] (hb : G.Colorable 2) (d : Nat) (hd : 0 < d)
    (hdegree : ∀ v, d ≤ G.degree v) :
    ∃ A B : Finset V, Disjoint A B ∧ A ∪ B = Finset.univ ∧
      G.IsBipartiteWith (↑A) (↑B) ∧ d ≤ A.card ∧ d ≤ B.card ∧ A.card ≤ B.card := by
  classical
  obtain ⟨s, t, hst⟩ := SimpleGraph.IsBipartite.exists_isBipartiteWith hb
  let A := s.toFinset
  let B := t.toFinset
  have hcross : G.IsBipartiteWith (↑A) (↑B) := by simpa [A, B] using hst
  have hdis : Disjoint A B := Finset.disjoint_coe.mp hcross.disjoint
  have hunion : A ∪ B = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro v
    have hp : 0 < G.degree v := lt_of_lt_of_le hd (hdegree v)
    obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp hp
    rcases hcross.mem_of_adj hvw with h | h
    · exact Finset.mem_union.mpr (Or.inl h.1)
    · exact Finset.mem_union.mpr (Or.inr h.1)
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨w, hvw⟩ := (G.degree_pos_iff_exists_adj v).mp (lt_of_lt_of_le hd (hdegree v))
  have hA : d ≤ A.card := by
    rcases hcross.mem_of_adj hvw with h | h
    · exact (hdegree w).trans (SimpleGraph.isBipartiteWith_degree_le' hcross h.2)
    · exact (hdegree v).trans (SimpleGraph.isBipartiteWith_degree_le' hcross h.1)
  have hB : d ≤ B.card := by
    rcases hcross.mem_of_adj hvw with h | h
    · exact (hdegree v).trans (SimpleGraph.isBipartiteWith_degree_le hcross h.1)
    · exact (hdegree w).trans (SimpleGraph.isBipartiteWith_degree_le hcross h.2)
  by_cases hAB : A.card ≤ B.card
  · exact ⟨A, B, hdis, hunion, hcross, hA, hB, hAB⟩
  · exact ⟨B, A, hdis.symm, by simpa [Finset.union_comm] using hunion,
      hcross.symm, hB, hA, by omega⟩

theorem parts_card_sum (A B : Finset V) (hd : Disjoint A B)
    (hu : A ∪ B = Finset.univ) : A.card + B.card = Fintype.card V := by
  rw [← Finset.card_union_of_disjoint hd, hu, Finset.card_univ]

theorem regular_fourteen_order (G : SimpleGraph V) [DecidableRel G.Adj]
    (hb : G.Colorable 2) (hnlo : 28 ≤ Fintype.card V) (hnhi : Fintype.card V ≤ 31)
    (hdegree : ∀ v, G.degree v = 14) : Fintype.card V = 28 ∨ Fintype.card V = 30 := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨A, B, hdis, hunion, hcross, hA, hB, hAB⟩ :=
    exists_ordered_parts G hb 14 (by decide) (fun v => by rw [hdegree])
  have hbalance := SimpleGraph.isBipartiteWith_sum_degrees_eq hcross
  simp only [hdegree, Finset.sum_const, smul_eq_mul] at hbalance
  have hcard := parts_card_sum A B hdis hunion
  omega

omit [DecidableEq V] in
theorem fifteen_count_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegrees : ∀ v, G.degree v = 15 ∨ G.degree v = 16) (A : Finset V) :
    (∑ v ∈ A, G.degree v) + (A.filter fun v => G.degree v = 15).card = 16 * A.card := by
  classical
  have hsum : (∑ v ∈ A, (G.degree v + if G.degree v = 15 then 1 else 0)) =
      ∑ _v ∈ A, 16 := by
    apply Finset.sum_congr rfl
    intro v _
    rcases hdegrees v with h | h <;> simp [h]
  simpa only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id, Finset.sum_const,
    smul_eq_mul, Nat.mul_comm] using hsum

theorem fifteen_filter_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V) (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (Finset.univ.filter fun v => G.degree v = 15).card =
      (A.filter fun v => G.degree v = 15).card +
      (B.filter fun v => G.degree v = 15).card := by
  classical
  rw [← hu, Finset.filter_union, Finset.card_union_of_disjoint]
  exact hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

/-- The 31/33-vertex high complement has exactly 16 or 18 degree-15
vertices; in the 31-vertex case they form an independent set of size 16. -/
theorem high_graph_fifteen_cases (G : SimpleGraph V) [DecidableRel G.Adj]
    (hb : G.Colorable 2) (hn : Fintype.card V = 31 ∨ Fintype.card V = 33)
    (hdegrees : ∀ v, G.degree v = 15 ∨ G.degree v = 16) :
    let E := Finset.univ.filter fun v => G.degree v = 15
    (E.card = 16 ∨ E.card = 18) ∧
      (Fintype.card V = 31 → E.card = 16 ∧ G.IsIndepSet (↑E)) := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨A, B, hdis, hunion, hcross, hA, hB, hAB⟩ :=
    exists_ordered_parts G hb 15 (by decide) (fun v => by rcases hdegrees v with h|h <;> omega)
  let E := Finset.univ.filter fun v => G.degree v = 15
  change (E.card = 16 ∨ E.card = 18) ∧
    (Fintype.card V = 31 → E.card = 16 ∧ G.IsIndepSet (↑E))
  have hcard := parts_card_sum A B hdis hunion
  have hbalance := SimpleGraph.isBipartiteWith_sum_degrees_eq hcross
  have hsumA := fifteen_count_sum G hdegrees A
  have hsumB := fifteen_count_sum G hdegrees B
  have hE := fifteen_filter_partition G A B hdis hunion
  change E.card = _ at hE
  have heA := Finset.card_filter_le A (fun v => G.degree v = 15)
  have heB := Finset.card_filter_le B (fun v => G.degree v = 15)
  have haCases : A.card = 15 ∨ (A.card = 16 ∧ B.card = 17 ∧ Fintype.card V = 33) := by omega
  rcases haCases with ha | ⟨ha, hbsize, hn33⟩
  · have hbdeg : ∀ v ∈ B, G.degree v = 15 := by
      intro v hv
      have hle := SimpleGraph.isBipartiteWith_degree_le' hcross hv
      have hcases := hdegrees v
      omega
    have hbfilter : B.filter (fun v => G.degree v = 15) = B :=
      Finset.filter_eq_self.mpr hbdeg
    have hbSum : (∑ v ∈ B, G.degree v) = 15 * B.card := by
      calc
        _ = ∑ _v ∈ B, 15 := Finset.sum_congr rfl hbdeg
        _ = _ := by simp [Nat.mul_comm]
    have hn31 : Fintype.card V = 31 := by rw [hbfilter] at hE; omega
    have hb16 : B.card = 16 := by omega
    have hea0 : (A.filter fun v => G.degree v = 15).card = 0 := by omega
    have hE16 : E.card = 16 := by rw [hbfilter] at hE; omega
    refine ⟨Or.inl hE16, fun _ => ⟨hE16, ?_⟩⟩
    have hsub : E ⊆ B := by
      intro v hv
      have hv15 : G.degree v = 15 := (Finset.mem_filter.mp hv).2
      have huv : v ∈ A ∪ B := by rw [hunion]; exact Finset.mem_univ v
      rcases Finset.mem_union.mp huv with hva | hvb
      · have hm : v ∈ A.filter (fun v => G.degree v = 15) := Finset.mem_filter.mpr ⟨hva, hv15⟩
        have hempty := Finset.card_eq_zero.mp hea0
        rw [hempty] at hm; exact False.elim (Finset.notMem_empty _ hm)
      · exact hvb
    intro v hv w hw _ hadj
    have hvB := hsub hv
    have hwB := hsub hw
    have hvA := hcross.mem_of_mem_adj' hwB hadj
    exact Finset.disjoint_left.mp hdis hvA hvB
  · have hcount : E.card = 16 ∨ E.card = 18 := by omega
    exact ⟨hcount, by omega⟩

private theorem four_sizes_ninety (a b c d : Nat)
    (ha : a = 0 ∨ a = 28 ∨ a = 30) (hb : b = 0 ∨ b = 28 ∨ b = 30)
    (hc : c = 0 ∨ c = 28 ∨ c = 30) (hd : d = 0 ∨ d = 28 ∨ d = 30)
    (hs : a + b + c + d = 90) :
    (a = 0 ∧ b = 30 ∧ c = 30 ∧ d = 30) ∨
    (a = 30 ∧ b = 0 ∧ c = 30 ∧ d = 30) ∨
    (a = 30 ∧ b = 30 ∧ c = 0 ∧ d = 30) ∨
    (a = 30 ∧ b = 30 ∧ c = 30 ∧ d = 0) := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;> norm_num at *

end UniformCases

/-- The low-set sizes are now derived from the actual induced graph. -/
theorem synchronized_proper_low_card_cases (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    (lowColorVertices c q).card = 28 ∨ (lowColorVertices c q).card = 30 := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  have hb := synchronized_proper_low_bipartite c hc sync q hlow hhigh
  have hbounds := synchronized_proper_low_card c hc sync q hlow hhigh
  have hn : Fintype.card (↑(lowColorVertices c q) : Set (Fin 61)) =
      (lowColorVertices c q).card := Fintype.card_coe _
  have h := UniformCases.regular_fourteen_order _ hb (by omega) (by omega)
    (fun v => synchronized_low_induced_degree c hc sync q v)
  simpa only [hn] using h

def EVertices (c : Host) : Finset (Fin 61) := Finset.univ.filter fun v => W c v = 60

@[simp] theorem mem_EVertices (c : Host) (v : Fin 61) :
    v ∈ EVertices c ↔ W c v = 60 := by simp [EVertices]

theorem synchronized_degree_fifteen_iff_E (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (v : Fin 61) : colorDegree c q v = 15 ↔ v ∈ EVertices c := by
  rw [mem_EVertices]
  rcases sync.1 v with hC | hE
  · have hcases := W32_degree_cases c hc v hC q
    omega
  · exact ⟨fun _ => hE, fun _ => W60_degree_cases c hc v hE q⟩

theorem E_subset_high (c : Host) (hc : NoMonochromaticTriangle c)
    (q : FourColor) : EVertices c ⊆ (lowColorVertices c q)ᶜ := by
  intro v hv
  have hd := W60_degree_cases c hc v ((mem_EVertices c v).mp hv) q
  simp [hd]

/-- Identify the degree-15 vertices of the actual induced high graph with
the very same E vertices in the physical host. -/
theorem synchronized_proper_E_cases (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c)
    (q : FourColor) (hlow : (lowColorVertices c q).Nonempty)
    (hhigh : ((lowColorVertices c q)ᶜ).Nonempty) :
    ((EVertices c).card = 16 ∨ (EVertices c).card = 18) ∧
      ((lowColorVertices c q).card = 30 → (EVertices c).card = 16 ∧
        (colorGraph c q).IsIndepSet (↑(EVertices c))) := by
  classical
  letI : DecidableRel (colorGraph c q).Adj := Classical.decRel _
  let S := (lowColorVertices c q)ᶜ
  let G := (colorGraph c q).induce (↑S : Set (Fin 61))
  let EH : Finset {v // v ∈ S} := Finset.univ.filter fun v => G.degree v = 15
  have hdeg : ∀ v : {v // v ∈ S}, G.degree v = colorDegree c q v :=
    fun v => synchronized_high_induced_degree c hc sync q v
  have hdegrees : ∀ v, G.degree v = 15 ∨ G.degree v = 16 := by
    intro v
    rw [hdeg]
    have hnot14 : colorDegree c q v ≠ 14 := by simpa [S] using v.property
    have hcases := synchronized_degree_cases c hc sync q v
    omega
  have hcardS : S.card + (lowColorVertices c q).card = 61 := by
    simp [S, Nat.add_comm]
  have hn : Fintype.card {v // v ∈ S} = S.card := Fintype.card_coe _
  have hlowCases := synchronized_proper_low_card_cases c hc sync q hlow hhigh
  have horder : Fintype.card {v // v ∈ S} = 31 ∨ Fintype.card {v // v ∈ S} = 33 := by omega
  have hresults := UniformCases.high_graph_fifteen_cases G
    (synchronized_proper_high_bipartite c hc sync q hlow hhigh) horder hdegrees
  change (EH.card = 16 ∨ EH.card = 18) ∧
    (Fintype.card {v // v ∈ S} = 31 → EH.card = 16 ∧ G.IsIndepSet (↑EH)) at hresults
  have himage : EH.image Subtype.val = EVertices c := by
    ext v
    constructor
    · intro hv
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
      have h15 : G.degree w = 15 := (Finset.mem_filter.mp hw).2
      exact (synchronized_degree_fifteen_iff_E c hc sync q w).mp ((hdeg w).symm.trans h15)
    · intro hv
      let w : {v // v ∈ S} := ⟨v, E_subset_high c hc q hv⟩
      refine Finset.mem_image.mpr ⟨w, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [hdeg]
      exact (synchronized_degree_fifteen_iff_E c hc sync q v).mpr hv
  have hcardE : EH.card = (EVertices c).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  refine ⟨by simpa only [hcardE] using hresults.1, ?_⟩
  intro h30
  obtain ⟨h16, hind⟩ := hresults.2 (by omega)
  refine ⟨by simpa only [hcardE] using h16, ?_⟩
  intro v hv w hw hne hadj
  let v' : {v // v ∈ S} := ⟨v, E_subset_high c hc q hv⟩
  let w' : {v // v ∈ S} := ⟨w, E_subset_high c hc q hw⟩
  have hv' : v' ∈ EH := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hdeg]
    exact (synchronized_degree_fifteen_iff_E c hc sync q v).mpr hv
  have hw' : w' ∈ EH := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hdeg]
    exact (synchronized_degree_fifteen_iff_E c hc sync q w).mpr hw
  exact hind hv' hw' (by intro h; exact hne (congrArg Subtype.val h)) hadj

theorem C_low_color_card (c : Host) (hc : NoMonochromaticTriangle c)
    (v : Fin 61) (hv : W c v = 32) :
    (Finset.univ.filter fun q : FourColor => colorDegree c q v = 14).card = 2 := by
  have hsum := fourColor_degree_sum c v
  have ha := W32_degree_cases c hc v hv (false, false)
  have hb := W32_degree_cases c hc v hv (false, true)
  have hd := W32_degree_cases c hc v hv (true, false)
  have he := W32_degree_cases c hc v hv (true, true)
  have hbcard := Finset.sum_boole (R := Nat)
    (fun q : FourColor => colorDegree c q v = 14) Finset.univ
  simp only [Nat.cast_id] at hbcard
  rw [← hbcard]
  simp only [FourColor, Fintype.sum_prod_type, Fintype.sum_bool]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hd with hd | hd <;> rcases he with he | he <;> simp_all

/-- Double-count low memberships on the same four colors and61 vertices. -/
theorem synchronized_low_membership_sum (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c) :
    (∑ q : FourColor, (lowColorVertices c q).card) = 2 * (61 - (EVertices c).card) := by
  classical
  have hrows : ∀ v : Fin 61,
      (Finset.univ.filter fun q : FourColor => colorDegree c q v = 14).card =
        if W c v = 60 then 0 else 2 := by
    intro v
    rcases sync.1 v with hC | hE
    · rw [C_low_color_card c hc v hC, if_neg (by omega)]
    · simp [W60_degree_cases c hc v hE, hE]
  have hswap : (∑ q : FourColor, (lowColorVertices c q).card) =
      ∑ v : Fin 61, (Finset.univ.filter fun q : FourColor => colorDegree c q v = 14).card := by
    calc
      _ = ∑ q : FourColor, ∑ v : Fin 61,
          if colorDegree c q v = 14 then (1 : Nat) else 0 := by
        apply Finset.sum_congr rfl
        intro q _
        simpa only [Nat.cast_id, lowColorVertices] using
          (Finset.sum_boole (R := Nat) (fun v => colorDegree c q v = 14) Finset.univ).symm
      _ = ∑ v : Fin 61, ∑ q : FourColor,
          if colorDegree c q v = 14 then (1 : Nat) else 0 := Finset.sum_comm
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  rw [hswap]
  simp_rw [hrows]
  have hsum : (∑ v : Fin 61, if W c v = 60 then 0 else 2) =
      2 * (Finset.univ.filter fun v : Fin 61 => W c v ≠ 60).card := by
    rw [Finset.sum_ite]
    simp [Nat.mul_comm]
  rw [hsum]
  have hcE := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 61))) (p := fun v => W c v = 60)
  simp only [Finset.card_univ, Fintype.card_fin] at hcE
  change (EVertices c).card +
    (Finset.univ.filter fun v : Fin 61 => W c v ≠ 60).card = 61 at hcE
  omega

/-- Exclude every proper low-color set by the complete16/18 E-count
argument. Bipartitions and all counting premises are derived above. -/
theorem synchronized_no_proper_low_sets (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c) :
    ∀ q, lowColorVertices c q = ∅ ∨ lowColorVertices c q = Finset.univ := by
  classical
  intro q
  by_contra hq
  push Not at hq
  have hlow : (lowColorVertices c q).Nonempty := hq.1
  have hhigh : ((lowColorVertices c q)ᶜ).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    have := congrArg (fun s : Finset (Fin 61) => sᶜ) h
    simp only [compl_compl, compl_empty] at this
    exact hq.2 this
  have hEc := (synchronized_proper_E_cases c hc sync q hlow hhigh).1
  have hEnonempty : (EVertices c).Nonempty := Finset.card_pos.mp (by omega)
  have allHighNonempty : ∀ r, ((lowColorVertices c r)ᶜ).Nonempty := by
    intro r
    obtain ⟨v, hv⟩ := hEnonempty
    exact ⟨v, E_subset_high c hc r hv⟩
  have sizes : ∀ r, (lowColorVertices c r).card = 0 ∨
      (lowColorVertices c r).card = 28 ∨ (lowColorVertices c r).card = 30 := by
    intro r
    by_cases he : lowColorVertices c r = ∅
    · exact Or.inl (by simp [he])
    · exact Or.inr (synchronized_proper_low_card_cases c hc sync r
        (Finset.nonempty_iff_ne_empty.mpr he) (allHighNonempty r))
  have size30 : ∀ r, (lowColorVertices c r).card = 30 →
      (EVertices c).card = 16 ∧ (colorGraph c r).IsIndepSet (↑(EVertices c)) := by
    intro r hr
    exact (synchronized_proper_E_cases c hc sync r
      (Finset.card_pos.mp (by omega)) (allHighNonempty r)).2 hr
  have hsum := synchronized_low_membership_sum c hc sync
  simp only [FourColor, Fintype.sum_prod_type, Fintype.sum_bool] at hsum
  have h00 := sizes (false, false)
  have h01 := sizes (false, true)
  have h10 := sizes (true, false)
  have h11 := sizes (true, true)
  rcases hEc with h16 | h18
  · have hpatterns :
      ((lowColorVertices c (false,false)).card = 0 ∧
        (lowColorVertices c (false,true)).card = 30 ∧
        (lowColorVertices c (true,false)).card = 30 ∧
        (lowColorVertices c (true,true)).card = 30) ∨
      ((lowColorVertices c (false,false)).card = 30 ∧
        (lowColorVertices c (false,true)).card = 0 ∧
        (lowColorVertices c (true,false)).card = 30 ∧
        (lowColorVertices c (true,true)).card = 30) ∨
      ((lowColorVertices c (false,false)).card = 30 ∧
        (lowColorVertices c (false,true)).card = 30 ∧
        (lowColorVertices c (true,false)).card = 0 ∧
        (lowColorVertices c (true,true)).card = 30) ∨
      ((lowColorVertices c (false,false)).card = 30 ∧
        (lowColorVertices c (false,true)).card = 30 ∧
        (lowColorVertices c (true,false)).card = 30 ∧
        (lowColorVertices c (true,true)).card = 0) :=
      UniformCases.four_sizes_ninety _ _ _ _ h00 h01 h10 h11 (by omega)
    have hmissing : ∃ missing : FourColor, ∀ r, r ≠ missing →
        (lowColorVertices c r).card = 30 := by
      rcases hpatterns with h | h | h | h
      · refine ⟨(false,false), ?_⟩
        rintro ⟨a,b⟩ hne; cases a <;> cases b <;> simp_all
      · refine ⟨(false,true), ?_⟩
        rintro ⟨a,b⟩ hne; cases a <;> cases b <;> simp_all
      · refine ⟨(true,false), ?_⟩
        rintro ⟨a,b⟩ hne; cases a <;> cases b <;> simp_all
      · refine ⟨(true,true), ?_⟩
        rintro ⟨a,b⟩ hne; cases a <;> cases b <;> simp_all
    obtain ⟨missing, hmissing⟩ := hmissing
    have monochrome : ∀ v ∈ EVertices c, ∀ w ∈ EVertices c,
        v ≠ w → c v w = missing := by
      intro v hv w hw hne
      by_contra hcolor
      have hind := (size30 (c v w) (hmissing (c v w) hcolor)).2
      exact hind hv hw hne ⟨hne, rfl⟩
    obtain ⟨v,w,z,hv,hw,hz,hvw,hvz,hwz⟩ :=
      Finset.two_lt_card_iff.mp (show 2 < (EVertices c).card by omega)
    exact hc v w z ⟨hvw,hvz,hwz⟩
      ⟨(monochrome v hv w hw hvw).trans (monochrome v hv z hz hvz).symm,
        (monochrome v hv z hz hvz).trans (monochrome w hw z hz hwz).symm⟩
  · have no30 : ∀ r, (lowColorVertices c r).card ≠ 30 := by
      intro r hr; have := (size30 r hr).1; omega
    have hn00 := no30 (false,false)
    have hn01 := no30 (false,true)
    have hn10 := no30 (true,false)
    have hn11 := no30 (true,true)
    omega

/-- Full synchronized C/E-to-uniform conclusion, with no graph premise. -/
theorem synchronized_uniform_complete (c : Host)
    (hc : NoMonochromaticTriangle c) (sync : SynchronizedCE c) :
    ∃ high : Finset FourColor, high.card = 2 ∧
      ∀ v q, colorDegree c q v = if q ∈ high then 16 else 14 :=
  synchronized_uniform_of_no_proper_low_set c hc sync
    (synchronized_no_proper_low_sets c hc sync)


end Ramsey61
