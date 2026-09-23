import PricingABD.ABFixedColor
import PricingIntegration.NativeFrameClauses

set_option autoImplicit false
namespace PricingABD.ABBase
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABPosition PricingABD.ABFixedColor
open PricingIntegration.NativePrimaryCore PricingIntegration.NativePrimary PricingIntegration.NativeFrameClauses

theorem pairs_ordered {n : Nat} (p : Fin n×Fin n) (hp : p∈ABGeometry.orderedPairs n) : p.1<p.2 := by
  obtain ⟨u,_,he⟩:=List.mem_flatMap.mp hp
  obtain ⟨v,hv,rfl⟩:=List.mem_map.mp he
  exact of_decide_eq_true (List.mem_filter.mp hv).2

theorem template_source (l : Layout) (t : Types) (e : Edge l) (he : e∈templateEdges l t) :
    fixedColor l t e.1 e.2.1=some e.2.2 := by
  simp only [templateEdges,List.mem_append] at he
  rcases he with (hl|hr)|hm
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hl
    have hh:=fixedColor_encode t (Position.left p.1) (Position.left p.2)
    simpa only [encode,positionColor,if_neg (ne_of_lt (pairs_ordered p hp))] using hh
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hr
    have hh:=fixedColor_encode t (Position.right p.1) (Position.right p.2)
    simpa only [encode,positionColor,if_neg (ne_of_lt (pairs_ordered p hp))] using hh
  · obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hm
    have hh:=fixedColor_encode (l:=l) t (Position.marked p.1) (Position.marked p.2)
    simpa only [encode,positionColor,if_neg (ne_of_lt (pairs_ordered p hp))] using hh

theorem free_source (l : Layout) (t : Types) (e : Edge l) (he : e∈freeEdges l) :
    fixedColor l t e.1 e.2.1=some e.2.2 := by
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp he
  have hh:=fixedColor_encode t (Position.free p.1) (Position.free p.2)
  simpa only [encode,positionColor,if_neg (ne_of_lt (pairs_ordered p hp))] using hh

theorem mark_source (l : Layout) (t : Types) (e : Edge l) (he : e∈markEdges l) :
    fixedColor l t e.1 e.2.1=some e.2.2 := by
  obtain ⟨u,_,rfl⟩:=List.mem_map.mp he
  exact (fixedColor_encode (l:=l) t (Position.marked 15) (Position.free u)).trans (by simp [positionColor])

theorem fixed_source (l : Layout) (t : Types) (e : Edge l) (he : e∈fixedEdges l t) :
    fixedColor l t e.1 e.2.1=some e.2.2 := by
  simp only [fixedEdges,List.mem_append] at he
  rcases he with (ht|hf)|hm
  · exact template_source l t e ht
  · exact free_source l t e hf
  · exact mark_source l t e hm

theorem fixed_distinct (l : Layout) (t : Types) (e : Edge l) (he : e∈fixedEdges l t) : e.1≠e.2.1 := by
  intro h
  have hs:=fixed_source l t e he
  rw [h,fixedColor_diag] at hs
  contradiction

def units {l : Layout} (es : List (Edge l)) : CNF :=
  es.map (fun e=>[(true,PricingIntegration.NativePrimaryCore.edgeVar e.1 e.2.1 e.2.2)])
def forbidden (l : Layout) : CNF := (ABGeometry.orderedPairs (freeSize l)).map
  (fun p=>[(false,PricingIntegration.NativePrimaryCore.edgeVar (ABLayout.free l p.1) (ABLayout.free l p.2) 0)])
def physicalBase (l : Layout) (t : Types) : CNF :=
  PricingIntegration.NativeColoringClauses.physicalClauses (vertexCount l) ++
  PricingIntegration.NativeColoringClauses.triangleClauses (vertexCount l) ++
  units (templateEdges l t) ++ forbidden l ++ units (freeEdges l) ++ units (markEdges l)

theorem fixed_unit_sat {c : Host} {l : Layout} {t : Types} (f : Frame c l)
    (hg : Geometry t f) (e : Edge l) (he : e∈fixedEdges l t) :
    ClauseSat (primary f) [(true,PricingIntegration.NativePrimaryCore.edgeVar e.1 e.2.1 e.2.2)] := by
  refine ⟨(true,PricingIntegration.NativePrimaryCore.edgeVar e.1 e.2.1 e.2.2),by simp,?_⟩
  exact (primary_edge f _ _ _ (fixed_distinct l t e he)).mpr (fixed_sound f hg _ _ _ (fixed_source l t e he))

theorem units_sat {c : Host} {l : Layout} {t : Types} (f : Frame c l)
    (hg : Geometry t f) (es : List (Edge l)) (hsub : ∀e∈es,e∈fixedEdges l t) :
    FormulaSat (primary f) (units es) := by
  intro cl hcl
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hcl
  exact fixed_unit_sat f hg e (hsub e he)

theorem free_forbidden {c : Host} {l : Layout} (f : Frame c l) (hc : NoMonochromaticTriangle c) :
    FormulaSat (primary f) (forbidden l) := by
  intro cl hcl
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hcl
  have hne : ABLayout.free l p.1≠ABLayout.free l p.2:=(free_injective l).ne (ne_of_lt (pairs_ordered p hp))
  refine ⟨(false,PricingIntegration.NativePrimaryCore.edgeVar (ABLayout.free l p.1) (ABLayout.free l p.2) 0),by simp,?_⟩
  apply Bool.eq_false_iff.mpr
  intro hh
  have hcol:=(primary_edge f _ _ _ hne).mp hh
  have hu:=(f.spokes (ABLayout.free l p.1)).trans (congrArg palette (owner_free l p.1))
  have hv:=(f.spokes (ABLayout.free l p.2)).trans (congrArg palette (owner_free l p.2))
  exact hc f.root (f.vertex (ABLayout.free l p.1)) (f.vertex (ABLayout.free l p.2))
    ⟨(f.ne_root _).symm,(f.ne_root _).symm,f.vertex.injective.ne hne⟩ ⟨hu.trans hv.symm,hv.trans hcol.symm⟩

theorem base_sat {c : Host} {l : Layout} {t : Types} (f : Frame c l)
    (hc : NoMonochromaticTriangle c) (hg : Geometry t f) : FormulaSat (primary f) (physicalBase l t) := by
  simp only [physicalBase,formulaSat_append]
  exact ⟨⟨⟨⟨⟨primary_physical f,primary_triangles f hc⟩,
    units_sat f hg _ (by intro e he;simp [fixedEdges,he])⟩,free_forbidden f hc⟩,
    units_sat f hg _ (by intro e he;simp [fixedEdges,he])⟩,
    units_sat f hg _ (by intro e he;simp [fixedEdges,he])⟩

theorem units_below {l : Layout} (t : Types) (es : List (Edge l)) (hsub : ∀e∈es,e∈fixedEdges l t) :
    ∀cl∈units es,∀x∈cl,x.2<edgeLimit (vertexCount l) := by
  intro cl hcl x hx
  obtain ⟨e,he,rfl⟩:=List.mem_map.mp hcl
  have hx' : x=(true,PricingIntegration.NativePrimaryCore.edgeVar e.1 e.2.1 e.2.2) := by simpa using hx
  subst x
  exact (edgeVar_bounds (vertex_bounds l) _ _ _ (fixed_distinct l t e (hsub e he))).2

theorem forbidden_below (l : Layout) : ∀cl∈forbidden l,∀x∈cl,x.2<edgeLimit (vertexCount l) := by
  intro cl hcl x hx
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hcl
  have hx' : x=(false,PricingIntegration.NativePrimaryCore.edgeVar (ABLayout.free l p.1) (ABLayout.free l p.2) 0) := by simpa using hx
  subst x
  exact (edgeVar_bounds (vertex_bounds l) _ _ _ ((free_injective l).ne (ne_of_lt (pairs_ordered p hp)))).2

#print axioms base_sat
end PricingABD.ABBase
