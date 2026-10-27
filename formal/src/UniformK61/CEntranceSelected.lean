import UniformK61.CEntranceCatalogue
import CompletionC.NativeWholeReindex
import CompletionC.NativeSelectedBlocks

set_option autoImplicit false
set_option maxRecDepth 10000
namespace UniformK61.CEntrance
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.PairAdmission
open PricingC.NativeBlockActions PricingC.NativePairActions
open CompletionC.NativeMatrices CompletionC.NativeWholeReindex

/-- Reindex complete foreign cells, not just their selected supports. -/
noncomputable def reindexBlocks {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (f : Equiv.Perm (Fin (freeSize five))) (leftIndex rightIndex : Nat) : Blocks c five lt rt where
  entrance := b.entrance
  free := f.toEmbedding.trans b.free
  left := reindexModel true lt b.left leftIndex
  right := reindexModel true rt b.right rightIndex
  left_palette := b.left_palette
  right_palette := b.right_palette
  free_mem i := b.free_mem _
  free_own i := b.free_own _
  free_exact v := by
    rw [b.free_exact]
    constructor
    · rintro ⟨i,rfl⟩
      refine ⟨f.symm i,?_⟩
      change b.free (f (f.symm i)) = b.free i
      rw [Equiv.apply_symm_apply]
    · rintro ⟨i,rfl⟩
      exact ⟨f i,rfl⟩

noncomputable def combinedFree {five : Bool} (p : Fin 737) (i : Fin 600)
    (hf : freeSize five = (pairTable p).shape.free)
    (perm : Equiv.Perm (Fin (pairTable p).shape.free)) : Equiv.Perm (Fin (freeSize five)) :=
  (finCongr hf).trans ((CompletionC.NativeSelectedBlocks.factorFree p i).trans
    (perm.trans (finCongr hf.symm)))

noncomputable def selectedBlocks {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (p : Fin 737) (hf : freeSize five = (pairTable p).shape.free)
    (perm : Equiv.Perm (Fin (pairTable p).shape.free)) (i : Fin 600) : Blocks c five lt rt :=
  reindexBlocks b (combinedFree p i hf perm) (autoIndex (leftRole p i)) (autoIndex (rightRole p i))

noncomputable def freeFunction {c : Host} {five lt rt : Bool} (b : Blocks c five lt rt)
    (p : Fin 737) (hf : freeSize five = (pairTable p).shape.free)
    (perm : Equiv.Perm (Fin (pairTable p).shape.free)) (n : Nat) : Vertex :=
  if h : n < (pairTable p).shape.free then b.free ((finCongr hf.symm) (perm ⟨n,h⟩)) else b.entrance.root

/-- Evaluate the fixed native support order in any reindexed C blocks.
This uses no labeling or template for the fourteen marked-cell vertices. -/
noncomputable def supportVertex {c d : Host} {five lt rt lt' rt' : Bool}
    (b : Blocks c five lt rt) (s : Shape) (hf : freeSize five = s.free)
    (p : Fin 737) (hp : retained p = sourceRecord b s) (z : Blocks d five lt' rt')
    (a : Fin s.dimension) : Vertex :=
  if h0 : a.val < s.free then z.free ⟨a.val,by rw [hf]; exact h0⟩
  else if h1 : a.val < s.free+s.left then z.left.vertex
    ⟨digit leftOrders[p.val]! (a.val-s.free),left_label_bound b s p hp _ (by omega)⟩
  else z.right.vertex ⟨digit rightOrders[p.val]! (a.val-s.free-s.left),right_label_bound b s p hp _
    (by have h := Shape.dimension_sum s; have ha := a.isLt; omega)⟩

#print axioms selectedBlocks
end UniformK61.CEntrance
