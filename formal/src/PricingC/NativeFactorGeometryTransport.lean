import PricingC.NativeFactorGeometryData
namespace PricingC.NativeFactorGeometry
open PricingC.NativeBlockActions PricingC.NativeActionFactors
-- Prevent the elaborator from unfolding very large closed tables while matching
-- abstract equality hypotheses. The kernel still checks the same definitions.
attribute [local irreducible]
 PricingC.NativeActionFactors.freeSizesAt PricingC.NativeActionFactors.coordinateCodesAt
 PricingC.NativeActionFactors.freeCodesAt PricingC.NativeActionFactors.leftIdsAt
 PricingC.NativeActionFactors.rightIdsAt PricingC.NativeFactorGeometry.geometryIndicesAt
 PricingC.NativeActionFactors.freeSizes
 PricingC.NativeActionFactors.coordinateCodes PricingC.NativeActionFactors.freeCodes
 PricingC.NativeActionFactors.leftIds PricingC.NativeActionFactors.rightIds
 PricingC.NativeBlockActions.sizes PricingC.NativeBlockActions.inducedCodes
 PricingC.NativeFactorGeometry.freeSizes PricingC.NativeFactorGeometry.leftSizes
 PricingC.NativeFactorGeometry.rightSizes PricingC.NativeFactorGeometry.coordinateCodes
 PricingC.NativeFactorGeometry.freeCodes PricingC.NativeFactorGeometry.leftCodes
 PricingC.NativeFactorGeometry.rightCodes PricingC.NativeFactorGeometry.geometryIndices

theorem valid_of_bind (f:Fin 27280) (hg:Good (geometryOf f)) (hb:Bind f):NativeActionFactors.Valid f:=by
 obtain ⟨hf,hl,hr,hcode,hfc,hlc,hrc⟩:=hb
 rcases hg with ⟨hfree,hcount,hcoord⟩
 refine ⟨?_,?_,?_⟩
 · simpa only [hf,hfc] using hfree
 · simpa only [NativeActionFactors.count,hf,hl,hr] using hcount
 · intro i hi
   have hi':i.val<nf (geometryOf f)+nl (geometryOf f)+nr (geometryOf f):=by
    simpa only [NativeActionFactors.count,hf,hl,hr] using hi
   have hh:=hcoord i hi'
   simpa only [combinedCoordinate,inducedLabel,hcode,hf,hl,hr,hfc,hlc,hrc,combined] using hh
#print axioms valid_of_bind
end PricingC.NativeFactorGeometry
