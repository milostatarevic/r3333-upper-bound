import PricingABD.ABFixedColor
import PricingABD.KnownPull
import PricingIntegration.NativePrimary

set_option autoImplicit false
namespace PricingABD.ABKnown
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.DenseCounter PricingABD.ABLayout
open PricingABD.ABGeometry PricingABD.ABFixedColor
open PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary PricingIntegration.FoldedThreshold

structure Key (l : Layout) where
  u : Fin (vertexCount l)
  v : Fin (vertexCount l)
  q : Fin 4
  ordered : u<v

def code {l : Layout} (k : Key l) : Nat := orderedEdgeVar k.u k.v k.q

theorem code_injective (l : Layout) : Function.Injective (@code l) := by
  intro x y h
  obtain ⟨hu,hv,hq⟩:=orderedEdgeVar_injective (vertex_bounds l) x.u x.v y.u y.v x.q y.q x.ordered y.ordered h
  cases x;cases y;cases hu;cases hv;cases hq;rfl

def source {l : Layout} (t : Types) (k : Key l) : Option Bool :=
  (fixedColor l t k.u k.v).map (fun r=>decide (r=k.q))

noncomputable def known (l : Layout) (t : Types) : Known := KnownPull.pull (@code l) (source t)

theorem known_ordered (l : Layout) (t : Types) (u v : Fin (vertexCount l)) (q : Fin 4) (h : u<v) :
    known l t (orderedEdgeVar u v q)=(fixedColor l t u v).map (fun r=>decide (r=q)) :=
  KnownPull.at_code code (code_injective l) (source t) ⟨u,v,q,h⟩

theorem known_edge (l : Layout) (t : Types) (u v : Fin (vertexCount l)) (q : Fin 4) (hne : u≠v) :
    known l t (edgeVar u v q)=(fixedColor l t u v).map (fun r=>decide (r=q)) := by
  unfold PricingIntegration.NativePrimaryCore.edgeVar
  split_ifs with h
  · exact known_ordered l t u v q h
  · rw [known_ordered l t v u q (lt_of_le_of_ne (le_of_not_gt h) hne.symm),fixedColor_symm]

theorem known_high (l : Layout) (t : Types) (u : Fin (vertexCount l)) :
    known l t (high l u)=none := by
  apply KnownPull.outside
  intro k h
  have hb:=(orderedEdgeVar_bounds (vertex_bounds l) k.u k.v k.q k.ordered).2
  change orderedEdgeVar k.u k.v k.q=high l u at h
  dsimp [high] at h
  omega

theorem known_sound {c : Host} {l : Layout} {t : Types} (f : Frame c l) (hg : Geometry t f) :
    Sound (primary f) (known l t) := by
  apply KnownPull.sound
  intro k b hb
  unfold source at hb
  cases hs : fixedColor l t k.u k.v with
  | none => simp [hs] at hb
  | some r =>
    simp only [hs,Option.map_some,Option.some.injEq] at hb
    rw [←hb]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [code,primary_ordered f k.u k.v k.q k.ordered,fixed_sound f hg k.u k.v r hs]
    exact palette_injective.eq_iff

/-- The executable small-row source test; no large literal-address lookup. -/
def fixedTruth (l : Layout) (t : Types) (u v : Fin (vertexCount l)) (q : Fin 4) : Bool :=
  (fixedColor l t u v).any (fun r=>decide (r=q))

theorem known_isNone (l : Layout) (t : Types) (u v : Fin (vertexCount l)) (q : Fin 4) (hne : u≠v) :
    (knownValue (known l t) (true,edgeVar u v q)).isNone=(fixedColor l t u v).isNone := by
  rw [knownValue,known_edge l t u v q hne]
  cases fixedColor l t u v <;> rfl

theorem known_true (l : Layout) (t : Types) (u v : Fin (vertexCount l)) (q : Fin 4) (hne : u≠v) :
    (knownValue (known l t) (true,edgeVar u v q)==some true)=fixedTruth l t u v q := by
  rw [knownValue,known_edge l t u v q hne]
  unfold fixedTruth
  cases hs : fixedColor l t u v with
  | none => rfl
  | some r => by_cases h:r=q <;> simp [h]

#print axioms known_sound
#print axioms known_edge
end PricingABD.ABKnown
