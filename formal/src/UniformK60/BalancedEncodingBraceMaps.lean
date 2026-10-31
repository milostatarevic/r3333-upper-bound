import UniformK60.BalancedEncodingBraces
import UniformK60.UnitTransport

/-! The one simultaneous host and palette map used by all720 brace inputs. -/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace UniformK60.BalancedEncodingBraces
open Ramsey61 UniformK60.Physical
open UniformK60.Core (PhysicalUnit UnitMatches UnitsMatch unitsCNF)
open UniformK60.BalancedProjectedData

set_option maxRecDepth 100000 in
theorem cycle_bijective : ∀ kind, Function.Bijective (cycle kind) := by decide

theorem cycle_fixes_omitted : ∀ kind, cycle kind 15=15 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem cycle_colors : ∀ kind a b, a≠b →
    R4333.k16Template kind (cycle kind a) (cycle kind b) =
      ⟨((R4333.k16Template kind a b).val+1)%3,Nat.mod_lt _ (by decide)⟩ := by decide

theorem markedOrder_bijective : ∀ m, Function.Bijective (markedOrder m) := by decide

theorem markedOrder_last : ∀ m, markedOrder m 14=markedPosition m := by decide

theorem physicalColor_bijective : Function.Bijective physicalColor := by decide

-- The vertex map depends on a row only through its real-template kind.
def mapVertex (realKind : Bool) (m : MarkChoice) (v : Vertex) : Vertex :=
  if v.val=0 then 0 else if v.val≤28 then vertex (v.val+31)
  else if v.val≤44 then vertex (16+(cycle realKind ⟨(v.val-29)%16,Nat.mod_lt _ (by decide)⟩).val)
  else vertex (1+(cycle (markedKind m) (markedOrder m (coord (v.val-45))).castSucc).val)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem mapVertex_bijective : ∀ kind m, Function.Bijective (mapVertex kind m) := by decide

theorem physicalVertex_bijective (r : Row) (m : MarkChoice) :
    Function.Bijective (physicalVertex r m) := mapVertex_bijective (rowKind r) m

noncomputable def vertexEquiv (r : Row) (m : MarkChoice) : Vertex≃Vertex :=
  Equiv.ofBijective (physicalVertex r m) (physicalVertex_bijective r m)

noncomputable def paletteEquiv : Color≃Color := Equiv.ofBijective physicalColor physicalColor_bijective

/-- Every mapped fact is exactly the image of its own raw fact, with no
local edge recoloring and no identification of actual host vertices. -/
theorem mappedUnit_related (r : Row) (m : MarkChoice) (u : PhysicalUnit) :
    UnitTransport.Related (vertexEquiv r m).symm paletteEquiv (mappedUnit r m u) u := by
  refine ⟨rfl,?_,Or.inl ⟨?_,?_⟩⟩
  · exact (paletteEquiv.symm_apply_apply u.q).symm
  · exact ((vertexEquiv r m).symm_apply_apply u.u).symm
  · exact ((vertexEquiv r m).symm_apply_apply u.v).symm

theorem mapped_units_match (c : Coloring) (r : Row) (m : MarkChoice)
    (h : UnitsMatch c (rawUnits r m)) :
    UnitsMatch (UnitTransport.transformed c (vertexEquiv r m).symm paletteEquiv) (units (r,m)) := by
  intro u hu
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
  exact UnitTransport.related_matches c (vertexEquiv r m).symm paletteEquiv
    (mappedUnit r m v) v (h v hv) (mappedUnit_related r m v)

#print axioms mapped_units_match
end UniformK60.BalancedEncodingBraces
