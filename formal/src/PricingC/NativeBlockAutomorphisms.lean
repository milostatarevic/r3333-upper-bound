import PricingC.U15SupportCover
import PricingC.U16SupportCover
import PricingABD.T16SupportCover

namespace PricingC.NativeBlockAutomorphisms
inductive Kind where
 | u15 | t15 | u16 | t16
 deriving DecidableEq, Fintype

def order : Kind→Nat
 | .u15=>15 | .t15=>15 | .u16=>16 | .t16=>16

def template (k:Kind):R4333.EdgeColoring (Fin (order k)) (Fin 3):=
 match k with
 | .u15=>R4333.k15Untwisted
 | .t15=>R4333.k15Twisted
 | .u16=>R4333.k16Untwisted
 | .t16=>R4333.k16Twisted

noncomputable def auto (k:Kind) (i:Nat):Equiv.Perm (Fin (order k)):=
 match k with
 | .u15=>U15SupportCover.autoEquiv ⟨i%10,Nat.mod_lt _ (by decide)⟩
 | .t15=>if i%2=0 then Equiv.refl _ else PricingABD.FiniteSupportsFast.swap
 | .u16=>U16SupportCover.autoEquiv ⟨i%160,Nat.mod_lt _ (by decide)⟩
 | .t16=>PricingABD.T16SupportCover.autoEquiv ⟨i%32,Nat.mod_lt _ (by decide)⟩

theorem auto_preserves (k:Kind) (i:Nat) (a b:Fin (order k)) (hab:a≠b):
 template k (auto k i a) (auto k i b)=template k a b:=by
 cases k with
 | u15=>exact U15SupportCover.auto_preserves _ a b hab
 | u16=>exact U16SupportCover.auto_preserves _ a b hab
 | t16=>exact PricingABD.T16SupportCover.auto_preserves _ a b hab
 | t15=>
  unfold auto
  split_ifs
  · rfl
  · exact PricingABD.FiniteSupportsFast.swap_preserves a b hab

/-- Reindexing uses the entire original critical block, including every edge
to the exterior. This equation changes no physical graph or palette. -/
noncomputable def reindex {V:Type} (k:Kind) (i:Nat) (physical:Fin (order k)↪V):Fin (order k)↪V:=
 (auto k i).toEmbedding.trans physical

theorem reindex_preserves {V C:Type} (k:Kind) (i:Nat) (physical:Fin (order k)↪V)
 (host:V→V→C) (palette:Fin 3→C)
 (h:∀a b,a≠b → host (physical a) (physical b)=palette (template k a b)):
 ∀a b,a≠b → host (reindex k i physical a) (reindex k i physical b)=palette (template k a b):=by
 intro a b hab
 change host (physical (auto k i a)) (physical (auto k i b))=_
 rw[h _ _ ((auto k i).injective.ne hab),auto_preserves k i a b hab]

#print axioms reindex_preserves
end PricingC.NativeBlockAutomorphisms
