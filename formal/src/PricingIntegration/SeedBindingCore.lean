import Ramsey61.CConcreteFamily
import PricingG.Completion72

namespace PricingIntegration.SeedBinding
open Ramsey61 Ramsey61.CEncodingCore Ramsey61.CEncodingBase
open Ramsey61.CConcreteFamily PricingG.Completion72

deriving instance DecidableEq for PhysicalUnit

structure Metadata where
  states : Fin 3 → Fin 72
  maps : Fin 3 → Fin 16 → Option Vertex

def scopePalette (s : Fin 3) : Fin 3 → Color :=
  ![![2,1,3], ![0,1,3], ![2,0,3]] s

def InS (m : Metadata) (v : Vertex) : Prop := ∃ a : Fin 16, m.maps 1 a = some v
instance (m : Metadata) (v : Vertex) : Decidable (InS m v) :=
  inferInstanceAs (Decidable (∃ a : Fin 16, m.maps 1 a = some v))

/-- The exact geometric data needed by a seed. All three scopes use one host
coloring and the original fixed palettes. -/
structure Geometry (c : Host) (m : Metadata) : Prop where
  root : RootConditions c
  template : ∀ s a b u v, m.maps s a = some u → m.maps s b = some v →
    u ≠ v → c u v = palette (scopePalette s (referenceColor (m.states s) a b))
  membership : ∀ v, v ∈ colorNeighborhood c (palette 2) 33 ↔ InS m v

inductive Origin where
  | root (v : Vertex) (q : Color)
  | template (s : Fin 3) (a b : Fin 16)
  | marked (v : Vertex)
  deriving DecidableEq

def orderedUnit (positive : Bool) (u v : Vertex) (q : Color) : PhysicalUnit :=
  if u ≤ v then ⟨positive,u,v,q⟩ else ⟨positive,v,u,q⟩

def decode (m : Metadata) : Origin → PhysicalUnit
  | .root v q => orderedUnit true 0 v q
  | .template s a b => orderedUnit true ((m.maps s a).getD 0) ((m.maps s b).getD 0)
      (scopePalette s (referenceColor (m.states s) a b))
  | .marked v => orderedUnit (decide (InS m v)) 33 v 2

def Valid (m : Metadata) : Origin → Prop
  | .root v q => v ≠ 0 ∧ v ∈ rootBlocks q
  | .template s a b => (m.maps s a).isSome = true ∧ (m.maps s b).isSome = true ∧
      (m.maps s a).getD 0 ≠ (m.maps s b).getD 0
  | .marked v => v ≠ 33

instance (m : Metadata) (o : Origin) : Decidable (Valid m o) := by
  cases o <;> unfold Valid <;> infer_instance

theorem orderedUnit_matches (c : Host) (positive : Bool) (u v : Vertex) (q : Color)
    (hne : u ≠ v)
    (hc : if positive then c u v = palette q else c u v ≠ palette q) :
    UnitMatches c (orderedUnit positive u v q) := by
  unfold orderedUnit
  split_ifs
  · exact ⟨hne,hc⟩
  · refine ⟨hne.symm, ?_⟩
    simpa only [c.color_symm v u] using hc

theorem decode_matches (c : Host) (m : Metadata) (hg : Geometry c m)
    (o : Origin) (ho : Valid m o) : UnitMatches c (decode m o) := by
  cases o with
  | root v q =>
    apply orderedUnit_matches c true 0 v q ho.1.symm
    exact hg.root.1 q v ho.2
  | template s a b =>
    apply orderedUnit_matches c true _ _ _ ho.2.2
    apply hg.template s a b _ _ _ _ ho.2.2
    · cases h : m.maps s a with
      | none => simp [Valid,h] at ho
      | some u => simp [h]
    · cases h : m.maps s b with
      | none => simp [Valid,h] at ho
      | some u => simp [h]
  | marked v =>
    apply orderedUnit_matches c (decide (InS m v)) 33 v 2 ho.symm
    by_cases hv : InS m v
    · have h := (hg.membership v).mpr hv
      simpa only [hv, decide_true, if_true] using (mem_colorNeighborhood _ _ _ _).mp h |>.2
    · have h : c 33 v ≠ palette 2 := by
        intro he
        exact hv ((hg.membership v).mp ((mem_colorNeighborhood _ _ _ _).mpr ⟨ho,he⟩))
      simpa only [hv, decide_false, Bool.false_eq_true, if_false] using h

/-- Linear origin checks bind every literal of the stored seed to the exact
geometric assertion that justifies it; no SAT computation is used. -/
theorem origins_supply_seed (c : Host) (i : Fin 456) (m : Metadata)
    (origins : List Origin) (hg : Geometry c m)
    (hvalid : ∀ o ∈ origins, Valid m o)
    (heq : origins.map (decode m) = seedData i) : SeedMatches c i := by
  intro u hu
  rw [←heq] at hu
  obtain ⟨o,ho,rfl⟩ := List.mem_map.mp hu
  exact decode_matches c m hg o (hvalid o ho)

#print axioms origins_supply_seed
end PricingIntegration.SeedBinding
