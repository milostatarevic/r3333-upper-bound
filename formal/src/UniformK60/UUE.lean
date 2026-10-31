import UniformK60.UUMarkedTransport

set_option autoImplicit false
namespace UniformK60.UUE
open Ramsey61 UniformK61.Core UniformK61.UUBridgeData UniformK61.UUSupportData
open UniformK60.UUSourceFacts UniformK60.UnitRestriction

def omitted (r : Fin 15) : Omission := ⟨45+r.val,by omega⟩

theorem source_preimage (q : Bool) (a : Action) (source : Fin 15) :
    ∃ r : Fin 15,UniformK61.UUBridgeData.vertices q a (omitted r).castSucc=(omitted source).castSucc := by
  let π := UniformK61.UUBridgeData.vertices q a
  let y := π.symm (omitted source).castSucc
  have hy : π y=(omitted source).castSucc := π.apply_symm_apply _
  have hlo : 45≤y.val := by
    by_contra h
    have hsmall := UniformK61.UUResidualTransport.backward_small_bound a q y (by omega)
    change (π y).val≤44 at hsmall
    rw [hy] at hsmall
    change 45+source.val≤44 at hsmall
    omega
  have hne : y≠60 := by
    intro he
    rw [he] at hy
    change backward a q 60=(omitted source).castSucc at hy
    rw [UniformK61.UUResidualTransport.backward_mark] at hy
    have hv := congrArg Fin.val hy
    change 60=45+source.val at hv
    omega
  have hhi : y.val<60 := by
    have := y.isLt
    have : y.val≠60 := fun h => hne (Fin.ext h)
    omega
  let r : Fin 15 := ⟨y.val-45,by omega⟩
  have he : (omitted r).castSucc=y := by
    apply Fin.ext
    dsimp [omitted,r]
    omega
  exact ⟨r,by rw [he];exact hy⟩

/-- An actual E reference reaches the same679 leaves and the frozen3/9
marked omissions, using only its good sixty-vertex restriction. -/
theorem reference_to_exact_E {q : Bool} {p : Pair} {i : Fin 600}
    {c : ReferenceColoring} (w : SourceFacts q p i c) (source : Fin 15)
    (hc : NoMonochromaticTriangle (restrictColoring c (omitted source))) :
    ∃ k : EFormula.Case,∃ v : DenseCounter.Valuation,DenseCounter.FormulaSat v (EFormula.formula k) := by
  let a := action p i
  let j := UniformK61.UUData.leaf (target p i)
  let d := UniformK61.UnitTransport.transformed c (UniformK61.UUBridgeData.vertices q a) (colors a)
  obtain ⟨r,hr⟩ := source_preimage q a source
  have hdgood := ReferenceExtension.restriction_transformed_good c (omitted source) (omitted r)
    (UniformK61.UUBridgeData.vertices q a) (colors a) hr hc
  have hdstatic := UniformK61.UUTemplateTransport.static_transport w.toStaticHost a
  have hdunits := UUFiniteBridge.transported_units w
  let π := UUMarkedTransport.vertices q r
  let e := UniformK61.UnitTransport.transformed d π (Equiv.refl _)
  let index := UUMarkedOmission.index q r
  have hegood := ReferenceExtension.restriction_transformed_good d (omitted r)
    (EFormula.omission q index) π (Equiv.refl _) (UUMarkedTransport.omission q r) hdgood
  have heunits := UUMarkedTransport.units hdstatic j hdunits r
  obtain ⟨v,hv⟩ := UnitRestriction.restriction_satisfiable e (EFormula.omission q index)
    (ReferenceSource.units (UniformK61.MarkedUU.caseUnits q j)) hegood (by
      intro u hu _
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hu
      exact (ReferenceSource.reference_matches e old).mpr (heunits old hold))
  exact ⟨Sum.inl ⟨q,j,index⟩,v,hv⟩

#print axioms reference_to_exact_E
end UniformK60.UUE
