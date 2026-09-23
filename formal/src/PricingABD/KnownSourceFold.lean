import PricingABD.BFixedGeometry
namespace PricingABD.KnownSourceFold
open Ramsey61 Ramsey61.DenseCounter Ramsey61.CEncodingCore
open PricingIntegration.FoldedThreshold
open PricingABD.BPhysicalBounds PricingABD.BPrimary PricingABD.BFixedGeometry
 def setKnown (k : Known) (fact : Nat × Bool) : Known :=
   Function.update k fact.1 (some fact.2)
 theorem update_sound (v : Valuation) (k : Known) (hk : Sound v k)
     (fact : Nat × Bool) (hf : v fact.1=fact.2) : Sound v (setKnown k fact) := by
   intro a b hab
   by_cases ha:a=fact.1
   · subst a
     have hb : fact.2=b := by simpa [setKnown] using hab
     exact hf.trans hb
   · have hb : k a=some b := by simpa [setKnown,ha] using hab
     exact hk a b hb
 theorem fold_sound (v : Valuation) (facts : List (Nat × Bool))
     (hf : ∀p∈facts,v p.1=p.2) (k : Known) (hk : Sound v k) :
     Sound v (facts.foldl setKnown k) := by
   induction facts generalizing k with
   | nil => exact hk
   | cons p ps ih =>
     apply ih (by intro q hq;exact hf q (by simp [hq]))
     exact update_sound v k hk p (hf p (by simp))
 def physicalFacts : List (Nat × Bool) := fixedEdges.flatMap fun e =>
   (List.finRange 4).map (fun q => (B52Core.edgeVar e.1 e.2.1 q,decide (q=e.2.2)))
 def knownFromSources : Known := physicalFacts.foldl setKnown (fun _ => none)
 theorem physical_sources_sound {c : Host} (f : Frame c) (hg : FixedGeometry f) :
     Sound (primary f) knownFromSources := by
   apply fold_sound
   · intro p hp
     obtain ⟨e,he,hp⟩ := List.mem_flatMap.mp hp
     obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
     exact fixed_known_value f hg e he q
   · intro a b h
     cases h
#print axioms physical_sources_sound
end PricingABD.KnownSourceFold
