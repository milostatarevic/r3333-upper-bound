import CompletionC.NativeRoleGeometry
import CompletionC.CommonBlocks
set_option autoImplicit false
namespace CompletionC.NativeWholeReindex
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.ClassificationAdapter
open PricingABD.ABLayout PricingABD.ABGeometry
open PricingC.NativeBlockAutomorphisms
open CompletionC.CommonBlocks CompletionC.NativeRoleGeometry

noncomputable def modelAuto (large twisted:Bool) (n:Nat):Equiv.Perm (Fin (if large then 16 else 15)):=by
 cases large <;> cases twisted
 · exact auto .u15 n
 · exact auto .t15 n
 · exact auto .u16 n
 · exact auto .t16 n

theorem modelAuto_preserves (large twisted:Bool) (n:Nat)
 (a b:Fin (if large then 16 else 15)) (hab:a≠b):
 model large twisted (modelAuto large twisted n a) (modelAuto large twisted n b)=model large twisted a b:=by
 cases large <;> cases twisted
 · exact auto_preserves .u15 n a b hab
 · exact auto_preserves .t15 n a b hab
 · exact auto_preserves .u16 n a b hab
 · exact auto_preserves .t16 n a b hab

theorem auto_cast_val {k j:Kind} (h:k=j) (n:Nat)
 (a:Fin (order k)) (b:Fin (order j)) (hab:a.val=b.val):
 (auto k n a).val=(auto j n b).val:=by
 subst j;exact congrArg (fun x:Fin (order k)=>(auto k n x).val) (Fin.ext hab)

theorem modelAuto_val (large twisted:Bool) (n:Nat)
 (a:Fin (order (modelKind large twisted))) (b:Fin (if large then 16 else 15))
 (hab:a.val=b.val):(auto (modelKind large twisted) n a).val=(modelAuto large twisted n b).val:=by
 cases large <;> cases twisted
 · exact congrArg (fun x:Fin 15=>(auto .u15 n x).val) (Fin.ext hab)
 · exact congrArg (fun x:Fin 15=>(auto .t15 n x).val) (Fin.ext hab)
 · exact congrArg (fun x:Fin 16=>(auto .u16 n x).val) (Fin.ext hab)
 · exact congrArg (fun x:Fin 16=>(auto .t16 n x).val) (Fin.ext hab)

noncomputable def reindexModel {c:Host} {r:Vertex} {q:Color} (large twisted:Bool)
 (m:PhysicalNeighborhoodMap c r (palette q) (model large twisted)) (n:Nat):
 PhysicalNeighborhoodMap c r (palette q) (model large twisted) where
 vertex:=(modelAuto large twisted n).toEmbedding.trans m.vertex
 mem_neighborhood i:=m.mem_neighborhood _
 covers_neighborhood v hv:=by
  obtain ⟨i,hi⟩:=m.covers_neighborhood v hv
  refine ⟨(modelAuto large twisted n).symm i,?_⟩
  change m.vertex (modelAuto large twisted n ((modelAuto large twisted n).symm i))=v
  simpa only[Equiv.apply_symm_apply] using hi
 colors:=m.colors
 map_color a b hab:=by
  change c (m.vertex (modelAuto large twisted n a)) (m.vertex (modelAuto large twisted n b))=_
  rw[m.map_color _ _ ((modelAuto large twisted n).injective.ne hab),modelAuto_preserves large twisted n a b hab]

/-- A native factor acts on whole critical cells and the entire free set;
it preserves one physical host, root, marked vertex, types and selection. -/
noncomputable def reindexBlocks {c:Host} {l:Layout} {t:Types} (b:Blocks c l t)
 (f:Equiv.Perm (Fin (freeSize l))) (leftIndex rightIndex:Nat):Blocks c l t where
 root:=b.root
 free:=f.toEmbedding.trans b.free
 left:=reindexModel (leftLarge l) t.left b.left leftIndex
 right:=reindexModel (rightLarge l) t.right b.right rightIndex
 marked:=b.marked
 free_mem i:=b.free_mem _
 left_palette:=b.left_palette
 right_palette:=b.right_palette
 marked_palette:=b.marked_palette
 low_degree:=b.low_degree
 selected:=b.selected
 marked_high:=b.marked_high
 free_own i:=b.free_own _
 free_exact v:=by
  rw[b.free_exact]
  constructor
  · rintro ⟨i,rfl⟩;refine ⟨f.symm i,?_⟩
    change b.free (f (f.symm i))=b.free i
    rw[Equiv.apply_symm_apply]
  · rintro ⟨i,rfl⟩;exact ⟨f i,rfl⟩
#print axioms reindexBlocks
#print axioms modelAuto_preserves
end CompletionC.NativeWholeReindex
