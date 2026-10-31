import UniformK60.BalancedHostBracePlacement
import UniformK60.BalancedHostBraceMembership

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK60.BalancedHostBraceCoordinates
open Ramsey61 UniformK60.Physical
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite
open UniformK60.BalancedProjectedHost UniformK60.BalancedHostBraceFrame
open UniformK60.BalancedHostBraceRow UniformK60.BalancedHostBracePlacement
open UniformK60.BalancedHostBraceMembership UniformK60.BalancedEncodingBraces
open CompletionC.NativeMatrices

/-- All three support groups use the same physical placement as the complete
real template. The full16 coherence is essential in the last case. -/
theorem placed_support {c : Host} {root mark : Vertex} {g : Geometry}
    (a : ActualFrame c root mark g) (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600)
    (e : Vertex≃Vertex)
    (hf : ∀ j,e (freeVertex (rowFreeSizeLe (target g i)) j)=rowFree a p i j)
    (hfake : ∀ j,e (fakeVertex j)=rowFake a p i j)
    (hr : ∀ j,e (realVertex j)=(rowReal a i).vertex j)
    (v : Fin 15) (hv : v.val<(rowShape (target g i)).dimension) :
    e (rawSupport (target g i) v)=rowEmbedding g a.frame p i ⟨v.val,hv⟩ := by
  let r := target g i
  have hd := Shape.dimension_sum (rowShape r)
  have hleft := (row_dimensions r).1
  have hright := rowRealSizeLe r
  change e (rawSupport r v)=rowEmbedding g a.frame p i ⟨v.val,hv⟩
  unfold rawSupport
  by_cases h0 : v.val<freeSize r
  · simp only [if_pos h0]
    exact hf ⟨v.val,h0⟩
  · simp only [if_neg h0]
    by_cases h1 : v.val<freeSize r+5
    · simp only [if_pos h1]
      let j : Fin 5 := ⟨v.val-freeSize r,by omega⟩
      have he : vertex (15+v.val-freeSize r)=fakeVertex j := by
        apply congrArg vertex
        change 15+v.val-freeSize r=15+(v.val-freeSize r)
        omega
      rw [he,hfake]
      change rowEmbedding g a.frame p i (fakeIndex r j)=_
      apply congrArg (rowEmbedding g a.frame p i)
      apply Fin.ext
      change (rowShape r).free+(v.val-freeSize r)=v.val
      change freeSize r+(v.val-freeSize r)=v.val
      omega
    · simp only [if_neg h1]
      let j : Fin (rowShape r).right := ⟨v.val-freeSize r-5,by
        change v.val-(rowShape r).free-5<(rowShape r).right
        change ¬v.val<(rowShape r).free+5 at h1
        have hv' : v.val<(rowShape r).dimension := hv
        omega⟩
      let jj : Fin 5 := Fin.castLE (rowRealSizeLe r) j
      have hj : supportIndex (v.val-freeSize r-5)=jj := by
        apply Fin.ext
        change (v.val-freeSize r-5)%5=v.val-freeSize r-5
        apply Nat.mod_eq_of_lt
        have h:=j.isLt
        change v.val-freeSize r-5<(rowShape r).right at h
        omega
      rw [hj]
      change e (realVertex (rowRealSupport r jj))=_
      rw [hr]
      refine (row_real_vertex a p i j).symm.trans ?_
      apply congrArg (rowEmbedding g a.frame p i)
      apply Fin.ext
      change (rowShape r).free+5+(v.val-freeSize r-5)=v.val
      change freeSize r+5+(v.val-freeSize r-5)=v.val
      omega

#print axioms placed_support
end UniformK60.BalancedHostBraceCoordinates
