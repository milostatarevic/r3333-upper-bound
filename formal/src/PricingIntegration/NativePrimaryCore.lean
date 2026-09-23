import Ramsey61.CEncodingCore
import Ramsey61.DenseCounter

set_option autoImplicit false
namespace PricingIntegration.NativePrimaryCore
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter

def rowStart (n u : Nat) : Nat := u * (2*n-1-u) / 2
def edgeCount (n : Nat) : Nat := n*(n-1)/2
def edgeLimit (n : Nat) : Nat := 4*edgeCount n+1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_rows_separated : ∀ s : Fin 4, ∀ u v : Fin (50+s.val), u<v →
    rowStart (50+s.val) u.val + (50+s.val-1-u.val) ≤ rowStart (50+s.val) v.val := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem all_rows_bounded : ∀ s : Fin 4, ∀ u : Fin (50+s.val),
    rowStart (50+s.val) u.val + (50+s.val-1-u.val) ≤ edgeCount (50+s.val) := by
  decide +kernel

theorem rowStart_separated {n : Nat} (hn : 50≤n ∧ n≤53) (u v : Fin n) (h : u<v) :
    rowStart n u.val + (n-1-u.val) ≤ rowStart n v.val := by
  let s : Fin 4 := ⟨n-50,by omega⟩
  have he : 50+s.val=n := by dsimp [s];omega
  let u' : Fin (50+s.val) := ⟨u.val,by rw [he];exact u.isLt⟩
  let v' : Fin (50+s.val) := ⟨v.val,by rw [he];exact v.isLt⟩
  have hh := all_rows_separated s u' v' h
  simpa only [u',v',he] using hh

theorem rowStart_bounded {n : Nat} (hn : 50≤n ∧ n≤53) (u : Fin n) :
    rowStart n u.val + (n-1-u.val) ≤ edgeCount n := by
  let s : Fin 4 := ⟨n-50,by omega⟩
  have he : 50+s.val=n := by dsimp [s];omega
  let u' : Fin (50+s.val) := ⟨u.val,by rw [he];exact u.isLt⟩
  have hh := all_rows_bounded s u'
  simpa only [u',he] using hh

theorem edgeLimit_python {n : Nat} (hn : 50≤n ∧ n≤53) :
    edgeLimit n=2*n*(n-1)+1 := by
  obtain ⟨hlo,hhi⟩:=hn
  interval_cases n <;> decide

def edgeRank {n : Nat} (u v : Fin n) : Nat := rowStart n u.val + (v.val-u.val-1)
def orderedEdgeVar {n : Nat} (u v : Fin n) (q : Fin 4) : Nat := 4*edgeRank u v+q.val+1
def edgeVar {n : Nat} (u v : Fin n) (q : Fin 4) : Nat :=
  if u<v then orderedEdgeVar u v q else orderedEdgeVar v u q

theorem edgeRank_bounds {n : Nat} (u v : Fin n) (h : u<v) :
    rowStart n u.val ≤ edgeRank u v ∧ edgeRank u v < rowStart n u.val+(n-1-u.val) := by
  have hv:=v.isLt
  change u.val<v.val at h
  unfold edgeRank
  omega

theorem edgeRank_injective {n : Nat} (hn : 50≤n ∧ n≤53)
    (u v x y : Fin n) (huv : u<v) (hxy : x<y) (he : edgeRank u v=edgeRank x y) :
    u=x ∧ v=y := by
  have hb:=edgeRank_bounds u v huv
  have hc:=edgeRank_bounds x y hxy
  have hux : u=x := by
    rcases lt_trichotomy u x with h|h|h
    · have hs:=rowStart_separated hn u x h;omega
    · exact h
    · have hs:=rowStart_separated hn x u h;omega
  subst x
  refine ⟨rfl,Fin.ext ?_⟩
  change u.val<v.val at huv
  change u.val<y.val at hxy
  unfold edgeRank at he
  omega

theorem orderedEdgeVar_injective {n : Nat} (hn : 50≤n ∧ n≤53)
    (u v x y : Fin n) (q r : Fin 4) (huv : u<v) (hxy : x<y)
    (he : orderedEdgeVar u v q=orderedEdgeVar x y r) : u=x ∧ v=y ∧ q=r := by
  have hq:=q.isLt
  have hr:=r.isLt
  have he':=he
  unfold orderedEdgeVar at he'
  have hRank : edgeRank u v=edgeRank x y := by omega
  obtain ⟨hu,hv⟩:=edgeRank_injective hn u v x y huv hxy hRank
  exact ⟨hu,hv,Fin.ext (by omega)⟩

theorem orderedEdgeVar_bounds {n : Nat} (hn : 50≤n ∧ n≤53)
    (u v : Fin n) (q : Fin 4) (huv : u<v) :
    1≤orderedEdgeVar u v q ∧ orderedEdgeVar u v q<edgeLimit n := by
  have hb:=edgeRank_bounds u v huv
  have hs:=rowStart_bounded hn u
  have hq:=q.isLt
  unfold orderedEdgeVar edgeLimit
  omega

theorem edgeVar_bounds {n : Nat} (hn : 50≤n ∧ n≤53)
    (u v : Fin n) (q : Fin 4) (hne : u≠v) : 1≤edgeVar u v q ∧ edgeVar u v q<edgeLimit n := by
  unfold edgeVar
  split_ifs with h
  · exact orderedEdgeVar_bounds hn u v q h
  · exact orderedEdgeVar_bounds hn v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm)

theorem edgeVar_symm {n : Nat} (u v : Fin n) (q : Fin 4) : edgeVar u v q=edgeVar v u q := by
  unfold edgeVar
  split_ifs <;> try rfl
  · omega
  · have he : u=v := by omega
    subst v;rfl

theorem orderedEdgeVar_python_formula {n : Nat} (hn : 50≤n ∧ n≤53)
    (u v : Fin n) (q : Fin 4) (huv : u<v) :
    orderedEdgeVar u v q=4*(u.val*(2*n-u.val-1)/2+v.val-u.val-1)+q.val+1 := by
  have hu:=u.isLt
  change u.val<v.val at huv
  have hsub : 2*n-u.val-1=2*n-1-u.val := by omega
  rw [hsub]
  unfold orderedEdgeVar edgeRank rowStart
  omega

abbrev Coloring (n : Nat) := EdgeColoring (Fin n) FourColor
noncomputable def physicalValuation {n : Nat} (c : Coloring n) : Valuation := by
  classical
  exact fun atom=>decide (∃u v : Fin n,∃q : Fin 4,u<v ∧ atom=orderedEdgeVar u v q ∧ c u v=palette q)

theorem physicalValuation_ordered {n : Nat} (hn : 50≤n ∧ n≤53)
    (c : Coloring n) (u v : Fin n) (q : Fin 4) (huv : u<v) :
    physicalValuation c (orderedEdgeVar u v q)=true ↔ c u v=palette q := by
  classical
  simp only [physicalValuation,decide_eq_true_eq]
  constructor
  · rintro ⟨x,y,r,hxy,he,hcol⟩
    obtain ⟨rfl,rfl,rfl⟩:=orderedEdgeVar_injective hn u v x y q r huv hxy he
    exact hcol
  · intro h;exact ⟨u,v,q,huv,rfl,h⟩

theorem physicalValuation_edge {n : Nat} (hn : 50≤n ∧ n≤53)
    (c : Coloring n) (u v : Fin n) (q : Fin 4) (hne : u≠v) :
    physicalValuation c (edgeVar u v q)=true ↔ c u v=palette q := by
  unfold edgeVar
  split_ifs with h
  · exact physicalValuation_ordered hn c u v q h
  · rw [physicalValuation_ordered hn c v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm),c.color_symm v u]

theorem physicalValuation_ordered_false {n : Nat} (hn : 50≤n ∧ n≤53)
    (c : Coloring n) (u v : Fin n) (q : Fin 4) (huv : u<v) :
    physicalValuation c (orderedEdgeVar u v q)=false ↔ c u v≠palette q := by
  rw [Bool.eq_false_iff]
  exact not_congr (physicalValuation_ordered hn c u v q huv)

#print axioms orderedEdgeVar_injective
#print axioms physicalValuation_edge
end PricingIntegration.NativePrimaryCore
