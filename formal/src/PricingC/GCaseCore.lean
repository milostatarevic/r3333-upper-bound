import PricingC.GRootNormalization
import PricingIntegration.CoreLayout

namespace PricingC.GIsomorphic
open Ramsey61 Ramsey61.CEncodingCore PricingG.Completion72 PricingC.AdjacentAutomorphisms
open PricingIntegration.CoreLayout

def nativeColor (i : Fin 72) := referenceColor (censusRow i)
def rootColor (i : Fin 2) := referenceColor (rootRow i)

set_option maxRecDepth 100000 in
theorem censusRow_bijective : Function.Bijective censusRow := by decide

def xPalette : Fin 3 → Color := ![1,2,3]
def yPalette : Fin 3 → Color := ![0,2,3]
def blockPoint (u : Fin 33) : Fin 16 := ⟨(u.val - 1) % 16, Nat.mod_lt _ (by decide)⟩

def crossColor (g : Fin 25) (x y : Fin 16) : Option Color :=
  if xorClebsch x y then some 1
  else if xorClebsch (retainedMap g x) y then some 0 else none

/-- Exact retained isomorphism core: one root, two physical16blocks,
fixed high cross edges, and two permitted low colors on every unknown. -/
def baseCore (x : Fin 2) (y : Fin 72) (g : Fin 25) : CoreBase := fun a b =>
  if a = b then none
  else if a = 0 then some (if b.val ≤ 16 then 0 else 1)
  else if b = 0 then some (if a.val ≤ 16 then 0 else 1)
  else if a.val ≤ 16 then
    if b.val ≤ 16 then some (xPalette (rootColor x (blockPoint a) (blockPoint b)))
    else crossColor g (blockPoint a) (blockPoint b)
  else if b.val ≤ 16 then crossColor g (blockPoint b) (blockPoint a)
  else some (yPalette (nativeColor y (blockPoint a) (blockPoint b)))

def caseX (i : Fin 3600) : Fin 2 := ⟨i.val / 1800,by omega⟩
def caseY (i : Fin 3600) : Fin 72 := ⟨i.val / 25 % 72,Nat.mod_lt _ (by decide)⟩
def caseG (i : Fin 3600) : Fin 25 := ⟨i.val % 25,Nat.mod_lt _ (by decide)⟩
def caseCore (i : Fin 3600) : CoreBase := baseCore (caseX i) (caseY i) (caseG i)

def caseIndex (x : Fin 2) (y : Fin 72) (g : Fin 25) : Fin 3600 :=
  ⟨x.val * 1800 + y.val * 25 + g.val,by omega⟩

theorem caseIndex_fields (x : Fin 2) (y : Fin 72) (g : Fin 25) :
    caseX (caseIndex x y g) = x ∧ caseY (caseIndex x y g) = y ∧ caseG (caseIndex x y g) = g := by
  refine ⟨?_,?_,?_⟩ <;> apply Fin.ext <;> dsimp [caseX,caseY,caseG,caseIndex] <;> omega

theorem caseCore_index (x : Fin 2) (y : Fin 72) (g : Fin 25) :
    caseCore (caseIndex x y g) = baseCore x y g := by
  obtain ⟨hx,hy,hg⟩ := caseIndex_fields x y g
  simp only [caseCore,hx,hy,hg]

#print axioms censusRow_bijective
#print axioms caseCore_index
end PricingC.GIsomorphic
