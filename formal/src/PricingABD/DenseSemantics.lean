import PricingABD.P15MatrixTransport

namespace PricingABD.DenseSemantics
open R4333.FiniteColorCNF PricingABD.P15Encoder PricingABD.P15Suffix PricingABD.P15MatrixTransport

def atom : Sat.Literal → Nat
  | .pos i => i
  | .neg i => i

def renameLiteral (map : Nat → Nat) : Sat.Literal → Sat.Literal
  | .pos i => .pos (map i)
  | .neg i => .neg (map i)

def renameClause (map : Nat → Nat) (c : Sat.Clause) : Sat.Clause := c.map (renameLiteral map)
def renameFmla (map : Nat → Nat) (f : Sat.Fmla) : Sat.Fmla := f.map (renameClause map)

theorem clause_renaming (v : Sat.Valuation) (encode decode : Nat → Nat) (c : Sat.Clause)
    (hinv : ∀ l, List.Mem l c →decode (encode (atom l))=atom l) :
    (show Sat.Valuation from fun d => v (decode d)).satisfies (renameClause encode c) ↔ v.satisfies c := by
  induction c with
  | nil => rfl
  | cons head tail ih =>
    have hhead := hinv head List.mem_cons_self
    have htail : ∀ l, List.Mem l tail →decode (encode (atom l))=atom l := fun l hl => hinv l (List.mem_cons_of_mem _ hl)
    have hn : (show Sat.Valuation from fun d => v (decode d)).neg (renameLiteral encode head) ↔ v.neg head := by
      cases head <;> dsimp only [atom] at hhead <;> simp only [renameLiteral,Sat.Valuation.neg,hhead]
    change ((show Sat.Valuation from fun d => v (decode d)).neg (renameLiteral encode head) →
      (show Sat.Valuation from fun d => v (decode d)).satisfies (renameClause encode tail)) ↔ (v.neg head → v.satisfies tail)
    rw [hn,ih htail]

theorem formula_renaming (v : Sat.Valuation) (encode decode : Nat → Nat) (f : Sat.Fmla)
    (hinv : ∀ c ∈ f,∀ l, List.Mem l c →decode (encode (atom l))=atom l)
    (hv : v.satisfies_fmla f) : (show Sat.Valuation from fun d => v (decode d)).satisfies_fmla (renameFmla encode f) := by
  constructor
  intro c hc
  obtain ⟨source,hsource,rfl⟩ := List.mem_map.mp hc
  exact (clause_renaming v encode decode source (hinv source hsource)).mpr (hv.prop source hsource)

def EdgeAtom (n k : Nat) (i : Nat) : Prop :=
  ∃ a b : Fin n,∃ q : Fin k,a<b ∧ i=edgeAtom a.val b.val q.val

def UsesEdges (n k : Nat) (f : Sat.Fmla) : Prop := ∀ c ∈ f,∀ l, List.Mem l c →EdgeAtom n k (atom l)

theorem uses_append {n k : Nat} {f g : Sat.Fmla} (hf : UsesEdges n k f) (hg : UsesEdges n k g) :
    UsesEdges n k (f++g) := by
  intro c hc l hl
  rcases List.mem_append.mp hc with hc | hc
  · exact hf c hc l hl
  · exact hg c hc l hl

theorem goodColoring_uses_edges (n k : Nat) : UsesEdges n k (goodColoringFmla n k) := by
  intro c hc l hl
  simp only [goodColoringFmla,List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · simp only [atLeastOneClauses,List.mem_map] at hc
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hl
    obtain ⟨ha,hb,hab⟩ := mem_edges_bounds hab
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨q,List.mem_range.mp hq⟩,hab,rfl⟩
  · simp only [atMostOneClauses,List.mem_flatMap,List.mem_map] at hc
    obtain ⟨⟨a,b⟩,hab,⟨q,r⟩,hqr,rfl⟩ := hc
    obtain ⟨ha,hb,hab⟩ := mem_edges_bounds hab
    obtain ⟨hq,hr,hqr⟩ := mem_edges_bounds hqr
    change l ∈ (show List Sat.Literal from _) at hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨q,hq⟩,hab,rfl⟩
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨r,hr⟩,hab,rfl⟩
  · simp only [triangleClauses,List.mem_flatMap,List.mem_map] at hc
    obtain ⟨⟨a,b,d⟩,habd,q,hq,rfl⟩ := hc
    obtain ⟨ha,hb,hd,hab,hbd⟩ := mem_triples_iff_bounds habd
    have hq := List.mem_range.mp hq
    change l ∈ (show List Sat.Literal from _) at hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact ⟨⟨a,ha⟩,⟨b,hb⟩,⟨q,hq⟩,hab,rfl⟩
    · exact ⟨⟨a,ha⟩,⟨d,hd⟩,⟨q,hq⟩,(show a<d from Nat.lt_trans hab hbd),rfl⟩
    · exact ⟨⟨b,hb⟩,⟨d,hd⟩,⟨q,hq⟩,hbd,rfl⟩

theorem positiveUnit_uses_edges {a b : Nat} (ha : a<50) (hb : b<50) (hab : a<b) (q : Fin 4) :
    UsesEdges 50 4 [positiveUnit a b q] := by
  intro c hc l hl
  simp only [List.mem_singleton] at hc
  subst c
  change l ∈ ([Sat.Literal.pos (edgeAtom a b q.val)] : List Sat.Literal) at hl
  simp only [List.mem_singleton] at hl
  subst l
  exact ⟨⟨a,ha⟩,⟨b,hb⟩,q,hab,rfl⟩

theorem physicalUnit_uses_edges (a b : Fin 50) (q : Fin 4) (hab : a≠b) :
    UsesEdges 50 4 [physicalUnit a b q] := by
  apply positiveUnit_uses_edges
  · exact lt_of_le_of_lt (min_le_left _ _) a.isLt
  · exact max_lt a.isLt b.isLt
  · have hn : a.val≠b.val := fun h => hab (Fin.ext h)
    omega

theorem suffix_uses_edges (p : Fin 14 ↪ Fin 50) (m : Fin 14 → Fin 14 → Fin 4) :
    UsesEdges 50 4 (suffix p m) := by
  intro c hc l hl
  simp only [suffix,List.mem_map] at hc
  obtain ⟨⟨a,b⟩,hab,rfl⟩ := hc
  obtain ⟨ha,hb,hab⟩ := mem_edges_bounds hab
  let i : Fin 14 := ⟨a,ha⟩
  let j : Fin 14 := ⟨b,hb⟩
  have hu := physicalUnit_uses_edges (p i) (p j) (m i j) (p.injective.ne (Fin.ne_of_lt hab))
  apply hu _ (List.mem_singleton_self _) l
  simpa only [i,j,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using hl

#print axioms formula_renaming
#print axioms goodColoring_uses_edges
#print axioms suffix_uses_edges
end PricingABD.DenseSemantics
