import UniformK61.BalancedEncodingLocal

set_option autoImplicit false
namespace UniformK61.BalancedEncoding
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open UniformK61.BalancedHost UniformK61.BalancedEncodingData
open PricingIntegration.BActualFrame

theorem physical_matches (c : Host) : PhysicalMatches (physicalValuation c) c := by
  intro u v huv q
  have h := physicalValuation_edge c u v q huv
  cases hh : physicalValuation c (edgeVar u v q) <;> simp_all

theorem physical_oneHot {c : Host} {v : Valuation} (hp : PhysicalMatches v c)
    (a b : Vertex) (hab : a ≠ b) : FormulaSat v (oneHot (edgeVar a b)) := by
  obtain ⟨q,hq⟩ := palette_surjective (c a b)
  apply oneHot_sat v _ q
  intro i
  rw [hp a b hab i,←hq]
  simp only [palette_injective.eq_iff]
  simp [eq_comm]

theorem spokes_sat {c : Host} {v : Valuation} (hp : PhysicalMatches v c) (hs : Spokes c) : FormulaSat v spokes := by
  apply sat_map
  intro u _
  exact ⟨positive (edgeVar 0 (BalancedHost.vertex u) (BalancedHost.rootColor u)),by simp,
    by simp [positive,hp _ _ (BalancedHost.vertex_ne_zero u).symm,hs u]⟩

theorem x_injective : Function.Injective xVertex := by intro a b h; have := congrArg Fin.val h; apply Fin.ext; simpa [xVertex] using this

theorem y_injective : Function.Injective yVertex := by intro a b h; have := congrArg Fin.val h; apply Fin.ext; simpa [yVertex] using this

theorem xy_ne (a b : Fin 16) : xVertex a ≠ yVertex b := by
  intro h; have := congrArg Fin.val h; simp only [xVertex,yVertex] at this; have := a.isLt; omega

theorem templates_sat {c : Host} {v : Valuation} {o : Owner} (hp : PhysicalMatches v c)
    (hn : Normalized c o.left o.right) : FormulaSat v (templates o) := by
  rw [templates,formulaSat_append]
  constructor
  · apply sat_map
    rintro ⟨a,b⟩ hpairs
    have hab := ne_of_lt (mem_pairs.mp hpairs)
    exact ⟨positive (edgeVar (xVertex a) (xVertex b) (foreign 0 (R4333.k16Template o.left a b))),by simp,by simp [positive,hp _ _ (x_injective.ne hab),hn.left_template a b hab]⟩
  · apply sat_map
    rintro ⟨a,b⟩ hpairs
    have hab := ne_of_lt (mem_pairs.mp hpairs)
    exact ⟨positive (edgeVar (yVertex a) (yVertex b) (foreign 1 (R4333.k16Template o.right a b))),by simp,by simp [positive,hp _ _ (y_injective.ne hab),hn.right_template a b hab]⟩

theorem grid_sat {c : Host} {v : Valuation} (hp : PhysicalMatches v c) : FormulaSat v gridOneHot := by
  apply sat_flatMap; intro x _
  exact sat_flatMap v _ _ fun y _ => physical_oneHot hp _ _ (xy_ne x y)

theorem triangle_pair_sat {c : Host} {v : Valuation} (hp : PhysicalMatches v c)
    (hc : NoMonochromaticTriangle c) (a b w : Vertex) (hab : a ≠ b) (haw : a ≠ w) (hbw : b ≠ w)
    (q : Color) (hfixed : c a b = palette q) :
    ClauseSat v [negative (edgeVar a w q),negative (edgeVar b w q)] := by
  by_cases ha : c a w = palette q
  · have hb : c b w ≠ palette q := fun hb => hc a b w ⟨hab,haw,hbw⟩ ⟨hfixed.trans ha.symm,ha.trans hb.symm⟩
    exact ⟨negative (edgeVar b w q),by simp,by simp [negative,hp _ _ hbw,hb]⟩
  · exact ⟨negative (edgeVar a w q),by simp,by simp [negative,hp _ _ haw,ha]⟩

theorem mixed_sat {c : Host} {v : Valuation} {o : Owner} (hp : PhysicalMatches v c)
    (hc : NoMonochromaticTriangle c) (hn : Normalized c o.left o.right) : FormulaSat v (mixedTriangles o) := by
  apply sat_flatMap
  rintro ⟨a,b⟩ hab
  have hab' := ne_of_lt (mem_pairs.mp hab)
  apply sat_flatMap
  intro m _
  intro clause hcl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hcl
  rcases hcl with rfl | rfl
  · exact triangle_pair_sat hp hc _ _ _ (x_injective.ne hab') (xy_ne a m) (xy_ne b m) _ (hn.left_template a b hab')
  · have hs := triangle_pair_sat hp hc _ _ _ (y_injective.ne hab') (xy_ne m a).symm (xy_ne m b).symm _ (hn.right_template a b hab')
    have edge_symm (u v : Vertex) (q : Color) : edgeVar u v q = edgeVar v u q := by
      unfold edgeVar
      by_cases h : u < v <;> by_cases h' : v < u <;> simp [h,h']
      · exact False.elim (not_lt_of_ge (le_of_lt h) h')
      · have he : u = v := le_antisymm (le_of_not_gt h') (le_of_not_gt h); subst v; rfl
    simpa only [edge_symm (yVertex a) (xVertex m),edge_symm (yVertex b) (xVertex m)] using hs

theorem selectors_sat {c : Host} {v : Valuation} {o : Owner} (hp : PhysicalMatches v c)
    (ws : Witnesses c o) (s : Scope) (hpattern : ∀ i,v (patternAtom s i) = decide (i=ws.pattern s)) :
    FormulaSat v (selectorClauses o s) := by
  rw [selectorClauses,formulaSat_append]
  refine ⟨oneHot_sat v _ (ws.pattern s) hpattern,?_⟩
  apply sat_flatMap; intro i _
  apply sat_map; intro m _
  by_cases hi : i = ws.pattern s
  · subst i
    refine ⟨(decide (m ∈ support (otherKind o s) (ws.pattern s)),guardAtom s m),by simp,?_⟩
    change v (guardAtom s m) = _
    simp only [guardAtom,hp _ _ (own_other_ne s _ _),ws.patterns s m]
  · exact ⟨negative (patternAtom s i),by simp,by simp [negative,hpattern i,hi]⟩

#print axioms mixed_sat
end UniformK61.BalancedEncoding
