import UniformK60.BalancedEncodingBlocks
import UniformK60.BalancedEncodingGuardBounds
import UniformK60.BalancedEncodingMerge

set_option autoImplicit false
namespace UniformK60.BalancedEncodingData
open Ramsey61 Ramsey61.DenseCounter UniformK60.Physical
open UniformK60.BalancedHost UniformK60.BalancedEncoding

def guardBlock (o : Owner) (s : Scope) : Block where
  lower := guardStart o s
  upper := guardStart o s+guardCount o s
  clauses := guardClauses (guardGeometry o s)

theorem guardBlocks_separate (o : Owner) (s t : Scope) (a : Nat)
    (hs : (guardBlock o s).owns a) (ht : (guardBlock o t).owns a) : s=t := by
  change guardStart o s<a ∧ a≤guardStart o s+guardCount o s at hs
  change guardStart o t<a ∧ a≤guardStart o t+guardCount o t at ht
  rcases lt_trichotomy s t with h | h | h
  · have hh := guard_separated o s t h;omega
  · exact h
  · have hh := guard_separated o t s h;omega

theorem guardBlock_support (o : Owner) (s : Scope) (clause : List Literal)
    (hc : clause∈(guardBlock o s).clauses) (lit : Literal) (hl : lit∈clause) :
    lit.2≤degreeTop o ∨ (guardBlock o s).owns lit.2 := by
  rcases guard_atoms (guardGeometry o s) clause hc lit hl with h | ⟨i,he⟩
  · exact Or.inl (by change lit.2≤122259;omega)
  · right
    rw [he]
    change guardStart o s<guardStart o s+i.val+1 ∧
      guardStart o s+i.val+1≤guardStart o s+guardCount o s
    have := i.isLt
    constructor <;> omega

theorem actual_guard_family_extension {c : Host} {o : Owner}
    (hc : NoMonochromaticTriangle c) (hn : Normalized false c o)
    (old : Valuation) (hp : PhysicalMatches old c) :
    ∃ w : Valuation,FormulaSat w (guards o) ∧
      ∀ a,a≤degreeTop o → w a=old a := by
  have local_sat (s : Scope) : ∃ w : Valuation,FormulaSat w (guardBlock o s).clauses ∧
      ∀ a,a≤degreeTop o → w a=old a := by
    obtain ⟨w⟩ := actual_guard_witness hc hn s
    have hi : Function.Injective (guardGeometry o s).selector := by
      intro i j he
      change guardStart o s+i.val+1=guardStart o s+j.val+1 at he
      exact Fin.ext (by omega)
    have hfresh (i) : degreeTop o<(guardGeometry o s).selector i := by
      have h := (guard_intervals o s).1
      change degreeTop o<guardStart o s+i.val+1
      omega
    obtain ⟨v,hv,ha,_⟩ := guard_extension old hp w (degreeTop o) (by change 7080≤122259;decide) hi hfresh
    exact ⟨v,hv,ha⟩
  exact blocks_satisfiable (guardBlock o) old (degreeTop o)
    (guardBlocks_separate o) (guardBlock_support o) local_sat

theorem guardTop_lower (o : Owner) : degreeTop o≤guardTop o := by
  have h := guard_intervals o 0
  omega

theorem guards_bound (o : Owner) (clause : List Literal) (hc : clause∈guards o)
    (lit : Literal) (hl : lit∈clause) : lit.2≤guardTop o := by
  obtain ⟨s,_,hs⟩ := List.mem_flatMap.mp hc
  apply guard_atoms_le (guardGeometry o s) (guardTop o) _ _ clause hs lit hl
  · have h := guardTop_lower o
    change 122259≤guardTop o at h
    omega
  · intro i
    have h := (guard_intervals o s).2
    have hi := i.isLt
    change guardStart o s+i.val+1≤guardTop o
    omega

#print axioms actual_guard_family_extension
end UniformK60.BalancedEncodingData
