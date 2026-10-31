import UniformK61.CNF

/-! Constructive soundness of the staggered sequential at-most counter.
The allocation and clause order are the PySAT seqcounter order used in the
frozen K60 mixed-balance prefixes. Only positive input atoms are needed. -/
set_option autoImplicit false
namespace UniformK60.SequentialCounter
open Ramsey61.DenseCounter

def prefixCount (b : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => prefixCount b i + if b i then 1 else 0

theorem prefix_mono (b : Nat → Bool) : Monotone (prefixCount b) := by
  apply monotone_nat_of_le_succ
  intro i
  simp only [prefixCount]
  omega

theorem prefix_eq_of_true (b : Nat → Bool) (n : Nat)
    (h : ∀ i < n, b i = true) : prefixCount b n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (by omega)
    rw [prefixCount, ih (fun i hi => h i (by omega)), hn]
    simp

/-- Zero-based columns; the first two rows are allocated interleaved. -/
def index (k d j : Nat) : Nat :=
  if d = 0 then 2*j else if d = 1 then 2*j+1 else d*k+j

def cell (top k d j : Nat) : Nat := top + 1 + index k d j

theorem index_injective (k d e j l : Nat) (hj : j < k) (hl : l < k)
    (h : index k d j = index k e l) : d = e ∧ j = l := by
  by_cases hd : d = 0 <;> by_cases he : e = 0
  · subst d; subst e; simp only [index, if_pos] at h; omega
  · subst d
    by_cases he1 : e = 1
    · subst e; simp [index] at h; omega
    · have hmul : 2*k ≤ e*k := Nat.mul_le_mul_right k (by omega)
      simp [index, he, he1] at h
      omega
  · subst e
    by_cases hd1 : d = 1
    · subst d; simp [index] at h; omega
    · have hmul : 2*k ≤ d*k := Nat.mul_le_mul_right k (by omega)
      simp [index, hd, hd1] at h
      omega
  · by_cases hd1 : d = 1 <;> by_cases he1 : e = 1
    · subst d; subst e; simp [index] at h; omega
    · subst d
      have hmul : 2*k ≤ e*k := Nat.mul_le_mul_right k (by omega)
      simp [index, he, he1] at h
      omega
    · subst e
      have hmul : 2*k ≤ d*k := Nat.mul_le_mul_right k (by omega)
      simp [index, hd, hd1] at h
      omega
    · simp only [index, hd, he, hd1, he1, if_false] at h
      have hdiv := congrArg (fun z => z / k) h
      have hk : 0 < k := by omega
      have hjdiv : j / k = 0 := Nat.div_eq_of_lt hj
      have hldiv : l / k = 0 := Nat.div_eq_of_lt hl
      rw [Nat.mul_comm d k, Nat.mul_comm e k, Nat.mul_add_div hk, Nat.mul_add_div hk, hjdiv, hldiv, Nat.add_zero, Nat.add_zero] at hdiv
      constructor
      · exact hdiv
      · subst e; omega

theorem index_lt (k m d j : Nat) (hm : 2 ≤ m) (hd : d < m) (hj : j < k) :
    index k d j < m*k := by
  have htwo : 2*k ≤ m*k := Nat.mul_le_mul_right k hm
  by_cases h0 : d = 0
  · simp [index, h0]; omega
  by_cases h1 : d = 1
  · simp [index, h1]; omega
  have hsucc : (d+1)*k ≤ m*k := Nat.mul_le_mul_right k (by omega)
  rw [Nat.add_mul] at hsucc
  simp only [Nat.one_mul] at hsucc
  simp only [index, h0, h1, if_false]
  omega

def step (x : Nat → Nat) (n k top d j : Nat) : CNF :=
  [(if j = 0 then [(false,x (d+j)),(true,cell top k d j)]
    else [(false,x (d+j)),(false,cell top k d (j-1)),(true,cell top k d j)])] ++
  (if d+1 < n-k then [[(false,cell top k d j),(true,cell top k (d+1) j)]] else [])

def regular (x : Nat → Nat) (n k top : Nat) : CNF :=
  (List.range (n-k)).flatMap fun d =>
    (List.range k).flatMap (step x n k top d) ++
    [[(false,x (d+k)),(false,cell top k d (k-1))]]

def counter (x : Nat → Nat) (n k top : Nat) : CNF :=
  if n ≤ k then [] else if k = 0 then
    (List.range n).map (fun i => [(false,x i)])
  else if k = n-1 then [(List.range n).map (fun i => (false,x i))]
  else regular x n k top

def finalTop (n k top : Nat) : Nat :=
  if n ≤ k ∨ k = 0 ∨ k = n-1 then top else top+(n-k)*k

/-- Cell threshold assignments suffice, independently of the physical meaning
of the input atoms. This is the constructive direction needed by the proof. -/
theorem regular_sat (v w : Valuation) (x : Nat → Nat) (n k top : Nat)
    (hk : 0 < k) (hn : k+1 < n)
    (inputs : ∀ i < n, w (x i) = v (x i))
    (bound : prefixCount (fun i => v (x i)) n ≤ k)
    (cells : ∀ d < n-k, ∀ j < k,
      w (cell top k d j) = decide (j+1 ≤ prefixCount (fun i => v (x i)) (d+j+1))) :
    FormulaSat w (regular x n k top) := by
  let b := fun i => v (x i)
  have mono := prefix_mono b
  intro clause hc
  obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
  have hdlt : d < n-k := List.mem_range.mp hd
  rcases List.mem_append.mp hc with hs | hcap
  · obtain ⟨j,hj,hclause⟩ := List.mem_flatMap.mp hs
    have hjlt : j < k := List.mem_range.mp hj
    have hi : d+j < n := by omega
    have hinput := inputs (d+j) hi
    rcases List.mem_append.mp hclause with hmain | hforward
    · simp only [List.mem_singleton] at hmain
      subst clause
      by_cases hbit : b (d+j) = true
      · have hb : prefixCount b (d+j+1) = prefixCount b (d+j)+1 := by simp [prefixCount,hbit]
        by_cases hj0 : j = 0
        · simp only [hj0,if_pos]
          refine ⟨(true,cell top k d 0),by simp,?_⟩
          rw [cells d hdlt 0 hk]
          simp only [decide_eq_true_eq]
          simpa only [hj0, Nat.add_zero] using (show 1 ≤ prefixCount b (d+j+1) by omega)
        · simp only [hj0,if_false]
          by_cases hprev : j ≤ prefixCount b (d+j)
          · refine ⟨(true,cell top k d j),by simp,?_⟩
            rw [cells d hdlt j hjlt]
            simp only [decide_eq_true_eq]
            change j+1 ≤ prefixCount b (d+j+1)
            omega
          · refine ⟨(false,cell top k d (j-1)),by simp,?_⟩
            rw [cells d hdlt (j-1) (by omega)]
            simp only [decide_eq_false_iff_not]
            have hidx : d+(j-1)+1=d+j := by omega
            rw [hidx]
            have hjidx : j-1+1=j := by omega
            rw [hjidx]
            exact hprev
      · have hbfalse : b (d+j) = false := by cases h : b (d+j) <;> simp_all
        refine ⟨(false,x (d+j)),?_,hinput.trans hbfalse⟩
        split <;> simp
    · by_cases hf : d+1 < n-k
      · simp only [hf,if_pos,List.mem_singleton] at hforward
        subst clause
        by_cases ht : j+1 ≤ prefixCount b (d+j+1)
        · refine ⟨(true,cell top k (d+1) j),by simp,?_⟩
          rw [cells (d+1) hf j hjlt]
          simp only [decide_eq_true_eq]
          exact le_trans ht (mono (by omega))
        · refine ⟨(false,cell top k d j),by simp,?_⟩
          rw [cells d hdlt j hjlt]
          exact decide_eq_false ht
      · simp [hf] at hforward
  · simp only [List.mem_singleton] at hcap
    subst clause
    have hi : d+k < n := by omega
    by_cases hbit : b (d+k) = true
    · refine ⟨(false,cell top k d (k-1)),by simp,?_⟩
      rw [cells d hdlt (k-1) (by omega)]
      apply decide_eq_false
      have hidx : d+(k-1)+1=d+k := by omega
      have hjidx : k-1+1=k := by omega
      rw [hidx,hjidx]
      change ¬ k ≤ prefixCount b (d+k)
      have hsum : prefixCount b (d+k+1) = prefixCount b (d+k)+1 := by simp [prefixCount,hbit]
      have hle := mono (show d+k+1 ≤ n by omega)
      change prefixCount b n ≤ k at bound
      omega
    · have hbfalse : b (d+k)=false := by cases h : b (d+k) <;> simp_all
      exact ⟨(false,x (d+k)),by simp,(inputs (d+k) hi).trans hbfalse⟩

/-- A finite cell assignment with freshness is extended by ordinary classical
choice; no executable evaluation or additional logical axiom is needed. -/
noncomputable def extend (v : Valuation) (x : Nat → Nat) (n k top : Nat) : Valuation :=
  fun a => if h : ∃ p : Fin (n-k) × Fin k, cell top k p.1 p.2 = a then
    decide ((Classical.choose h).2.val+1 ≤
      prefixCount (fun i => v (x i)) ((Classical.choose h).1.val+(Classical.choose h).2.val+1))
  else v a

theorem extend_below (v : Valuation) (x : Nat → Nat) (n k top a : Nat)
    (ha : a ≤ top) : extend v x n k top a = v a := by
  unfold extend
  split
  · rename_i h
    obtain ⟨p,hp⟩ := h
    unfold cell at hp
    omega
  · rfl

theorem extend_cells (v : Valuation) (x : Nat → Nat) (n k top : Nat)
    (d : Fin (n-k)) (j : Fin k) :
    extend v x n k top (cell top k d j) =
      decide (j.val+1 ≤ prefixCount (fun i => v (x i)) (d.val+j.val+1)) := by
  unfold extend
  split
  · rename_i h
    obtain ⟨hd,hj⟩ := index_injective k (Classical.choose h).1 d (Classical.choose h).2 j
      (Classical.choose h).2.isLt j.isLt
      (Nat.add_left_cancel (Classical.choose_spec h))
    simp only [hd,hj]
  · rename_i h
    exact False.elim (h ⟨(d,j),rfl⟩)

theorem satisfiable_extension (v : Valuation) (x : Nat → Nat) (n k top : Nat)
    (inputs_below : ∀ i < n, x i ≤ top)
    (bound : prefixCount (fun i => v (x i)) n ≤ k) :
    ∃ w : Valuation, (∀ a ≤ top, w a = v a) ∧ FormulaSat w (counter x n k top) := by
  by_cases hn : n ≤ k
  · refine ⟨v,fun _ _ => rfl,?_⟩
    simp [counter,hn,FormulaSat]
  by_cases hk : k = 0
  · refine ⟨v,fun _ _ => rfl,?_⟩
    rw [counter, if_neg hn, if_pos hk]
    intro clause hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi : i<n := List.mem_range.mp hi
    refine ⟨(false,x i),by simp,?_⟩
    by_cases hbit : v (x i)=true
    · have step := prefix_mono (fun j => v (x j)) (show i+1≤n by omega)
      simp [prefixCount,hbit] at step
      omega
    · cases h : v (x i) <;> simp_all
  by_cases hlast : k = n-1
  · refine ⟨v,fun _ _ => rfl,?_⟩
    rw [counter, if_neg hn, if_neg hk, if_pos hlast]
    intro clause hc
    have hc : clause=(List.range n).map (fun i => (false,x i)) := List.mem_singleton.mp hc
    subst clause
    have hex : ∃ i<n, v (x i)=false := by
      by_contra h
      have hall : ∀ i<n, v (x i)=true := by
        intro i hi
        cases hb : v (x i) <;> simp_all
      have heq := prefix_eq_of_true (fun i => v (x i)) n hall
      omega
    obtain ⟨i,hi,hbit⟩ := hex
    exact ⟨(false,x i),List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩,hbit⟩
  · refine ⟨extend v x n k top,?_,?_⟩
    · exact fun a ha => extend_below v x n k top a ha
    · simp only [counter,hn,hk,hlast,if_false]
      apply regular_sat v (extend v x n k top) x n k top (by omega) (by omega)
      · exact fun i hi => extend_below v x n k top (x i) (inputs_below i hi)
      · exact bound
      · intro d hd j hj
        exact extend_cells v x n k top ⟨d,hd⟩ ⟨j,hj⟩

theorem cell_le (top k m d j : Nat) (hm : 2 ≤ m) (hd : d < m) (hj : j < k) :
    cell top k d j ≤ top+m*k := by
  have h := index_lt k m d j hm hd hj
  unfold cell
  omega

theorem regular_atoms_le (x : Nat → Nat) (n k top : Nat)
    (hk : 0 < k) (hn : k+1 < n) (inputs : ∀ i<n, x i ≤ top)
    (clause : List Literal) (hc : clause ∈ regular x n k top)
    (lit : Literal) (hl : lit ∈ clause) : lit.2 ≤ top+(n-k)*k := by
  have hm : 2 ≤ n-k := by omega
  have input_bound : ∀ i<n, x i ≤ top+(n-k)*k :=
    fun i hi => le_trans (inputs i hi) (Nat.le_add_right _ _)
  have cell_bound : ∀ d<n-k, ∀ j<k, cell top k d j ≤ top+(n-k)*k :=
    fun d hd j hj => cell_le top k (n-k) d j hm hd hj
  obtain ⟨d,hd,hc⟩ := List.mem_flatMap.mp hc
  have hd : d<n-k := List.mem_range.mp hd
  rcases List.mem_append.mp hc with hs | hcap
  · obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hs
    have hj : j<k := List.mem_range.mp hj
    rcases List.mem_append.mp hc with hmain | hforward
    · have hmain := List.mem_singleton.mp hmain
      subst clause
      by_cases hzero : j=0
      · simp only [hzero,if_pos,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl
        · exact input_bound (d+0) (by omega)
        · exact cell_bound d hd 0 hk
      · simp only [hzero,if_false,List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl | rfl
        · exact input_bound (d+j) (by omega)
        · exact cell_bound d hd (j-1) (by omega)
        · exact cell_bound d hd j hj
    · by_cases hf : d+1<n-k
      · simp only [hf,if_pos,List.mem_singleton] at hforward
        subst clause
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl | rfl
        · exact cell_bound d hd j hj
        · exact cell_bound (d+1) hf j hj
      · simp [hf] at hforward
  · simp only [List.mem_singleton] at hcap
    subst clause
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact input_bound (d+k) (by omega)
    · exact cell_bound d hd (k-1) (by omega)

theorem counter_atoms_le (x : Nat → Nat) (n k top : Nat)
    (inputs : ∀ i<n, x i ≤ top) (clause : List Literal)
    (hc : clause ∈ counter x n k top) (lit : Literal) (hl : lit ∈ clause) :
    lit.2 ≤ finalTop n k top := by
  by_cases hn : n ≤ k
  · simp [counter,hn] at hc
  by_cases hk : k=0
  · rw [counter,if_neg hn,if_pos hk] at hc
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    have hi := List.mem_range.mp hi
    have hl := List.mem_singleton.mp hl
    subst lit
    simpa [finalTop,hk] using inputs i hi
  by_cases hlast : k=n-1
  · rw [counter,if_neg hn,if_neg hk,if_pos hlast] at hc
    have hc := List.mem_singleton.mp hc
    subst clause
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hl
    have hi := List.mem_range.mp hi
    simpa [finalTop,hlast] using inputs i hi
  · rw [counter,if_neg hn,if_neg hk,if_neg hlast] at hc
    have hb := regular_atoms_le x n k top (by omega) (by omega) inputs clause hc lit hl
    simpa [finalTop,hn,hk,hlast] using hb

#print axioms satisfiable_extension
#print axioms counter_atoms_le
end UniformK60.SequentialCounter
