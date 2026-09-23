import PricingABD.ABSourceRows
import PricingABD.ABRowCounts

set_option autoImplicit false
namespace PricingABD.ABSourceDomain
open PricingABD.ABLayout PricingABD.ABPosition PricingABD.ABGeometry PricingABD.ABFixedColor PricingABD.ABKnown PricingABD.ABSourceRows PricingABD.ABRowCounts
open PricingIntegration.NativePrimary

def positions (l : Layout) (includeFree : Bool) : List (Position l) :=
  (if includeFree then (List.finRange (freeSize l)).map Position.free else []) ++
  (List.finRange (leftSize l)).map Position.left ++
  (List.finRange (rightSize l)).map Position.right ++
  (List.finRange 16).map Position.marked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem positions_native (l : Layout) (includeFree : Bool) :
    (positions l includeFree).map encode=(if includeFree then allLabels l else tailLabels l) := by
  rcases l with ⟨p,b⟩
  cases p <;> cases b <;> cases includeFree <;> decide +kernel

def positionTruth {l : Layout} (t : Types) (u v : Position l) (q : Fin 4) : Bool :=
  (positionColor t u v).any (fun r=>decide (r=q))

@[simp] theorem fixedTruth_encode {l : Layout} (t : Types) (u v : Position l) (q : Fin 4) :
    fixedTruth l t (encode u) (encode v) q=positionTruth t u v q := by
  simp [fixedTruth,positionTruth]

 theorem fixedCount_unfiltered (l : Layout) (t : Types) (domain : List (Fin (vertexCount l)))
    (u : Fin (vertexCount l)) (q : Fin 4) :
    fixedCount l t domain u q=domain.countP (fun v=>fixedTruth l t u v q) := by
  rw [fixedCount,neighbors,List.countP_filter]
  apply List.countP_congr
  intro v _
  by_cases h : v=u
  · subst v;simp [fixedTruth]
  · simp [h]

 theorem fixedCount_positions (l : Layout) (t : Types) (includeFree : Bool)
    (u : Position l) (q : Fin 4) :
    fixedCount l t (if includeFree then allLabels l else tailLabels l) (encode u) q=
      (positions l includeFree).countP (fun v=>positionTruth t u v q) := by
  rw [fixedCount_unfiltered,←positions_native,List.countP_map]
  apply List.countP_congr
  intro v _
  simp only [Function.comp_apply,fixedTruth_encode]

#print axioms positions_native
#print axioms fixedCount_positions
end PricingABD.ABSourceDomain
