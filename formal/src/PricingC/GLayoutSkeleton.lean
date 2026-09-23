import PricingC.GLayoutRefinement

namespace PricingC.GIsomorphic
open Ramsey61 Ramsey61.CEncodingCore PricingIntegration.LocalRelations PricingIntegration.CoreLayout
open PricingC.GLayoutRefinement PricingG.Completion72

def coarseX (a b : Fin 16) : Option Color :=
 if a=b then some 1 else if xorClebsch a b then some 1 else none

def coarseY (a b : Fin 16) : Option Color :=
 if a=b then some 0 else if xorClebsch a b then some 0 else none

theorem erase_referenceX (i : Fin 72) (a b : Fin 16) :
 eraseLow (some (xPalette (referenceColor i a b)))=coarseX a b := by
 simp only [referenceColor,coarseX]
 split_ifs <;> rfl

theorem erase_referenceY (i : Fin 72) (a b : Fin 16) :
 eraseLow (some (yPalette (referenceColor i a b)))=coarseY a b := by
 simp only [referenceColor,coarseY]
 split_ifs <;> rfl

def fastSkeleton (g : Fin 25) : CoreBase := fun a b =>
 if a=b then none
 else if a=0 then some (if b.val≤16 then 0 else 1)
 else if b=0 then some (if a.val≤16 then 0 else 1)
 else if a.val≤16 then
  if b.val≤16 then coarseX (blockPoint a) (blockPoint b)
  else crossColor g (blockPoint a) (blockPoint b)
 else if b.val≤16 then crossColor g (blockPoint b) (blockPoint a)
 else coarseY (blockPoint a) (blockPoint b)

theorem fastSkeleton_exact (g : Fin 25) : fastSkeleton g=skeleton g := by
 funext a b
 simp only [fastSkeleton,skeleton,eraseCore,baseCore,rootColor,nativeColor]
 split_ifs <;> first
  | rfl
  | exact (erase_referenceX _ _ _).symm
  | exact (erase_referenceY _ _ _).symm
  | simp only [crossColor]; split_ifs <;> rfl

def OwnerValid (l : ScopeLayout) : Prop :=
 if l.side then 16<l.owner.val else 0<l.owner.val ∧ l.owner.val≤16

instance (l : ScopeLayout) : Decidable (OwnerValid l) := by
 unfold OwnerValid
 infer_instance

theorem layout_for_all_rows (g : Fin 25) (l : ScopeLayout)
 (h : LayoutValid (fastSkeleton g) l) (x : Fin 2) (y : Fin 72) :
 LayoutValid (baseCore x y g) l := by
 rw [fastSkeleton_exact] at h
 exact layoutValid_of_refines _ _ (baseCore_refines_skeleton x y g) l h

#print axioms fastSkeleton_exact
end PricingC.GIsomorphic
