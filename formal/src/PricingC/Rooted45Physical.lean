import PricingC.Rooted45Free
import PricingABD.P15PhysicalRooted

namespace PricingC.Rooted45Orientation
open Ramsey61 Ramsey61.CEncodingCore
open PricingABD.P15PhysicalRooted (threeIndex threeIndex_palette palette_threeIndex threeIndex_injective_on)

/-- One actual marked color3 neighborhood, with its root restored at14.
Only root incidences and the two foreign support patterns are prescribed;
the five free points have no prescribed internal coloring. -/
structure Physical45 (k : Bool) (c : Host) where
 mark : Vertex
 physical : Fin 15 ↪ Vertex
 mark_distinct : ∀i,mark≠physical i
 marked_edges : ∀i,c mark (physical i)=palette 3
 root_edges : ∀i,i≠14 → c (physical 14) (physical i)=palette (group k i).castSucc
 foreign_edges : ∀a b,a≠b → a≠14 → b≠14 → group k a≠0 → group k a=group k b →
  c (physical a) (physical b)=palette (interior k a b).castSucc

theorem physical_avoids_three {k : Bool} {c : Host} (f : Physical45 k c)
 (hc : NoMonochromaticTriangle c) (a b : Fin 15) (hab:a≠b) :
 c (f.physical a) (f.physical b)≠palette 3 := by
 intro he
 exact hc f.mark (f.physical a) (f.physical b)
  ⟨f.mark_distinct a,f.mark_distinct b,f.physical.injective.ne hab⟩
  ⟨(f.marked_edges a).trans (f.marked_edges b).symm,(f.marked_edges b).trans he.symm⟩

noncomputable def restoredColoring {k : Bool} {c : Host} (f : Physical45 k c) :
 R4333.EdgeColoring (Fin 15) (Fin 3) where
 color a b:=threeIndex (c (f.physical a) (f.physical b))
 color_symm a b:=congrArg threeIndex (c.color_symm _ _)

theorem restored_good {k : Bool} {c : Host} (f : Physical45 k c)
 (hc : NoMonochromaticTriangle c) : R4333.NoMonochromaticTriangle (restoredColoring f) := by
 intro a b d hd hm
 apply hc (f.physical a) (f.physical b) (f.physical d)
  ⟨f.physical.injective.ne hd.1,f.physical.injective.ne hd.2.1,f.physical.injective.ne hd.2.2⟩
 exact ⟨threeIndex_injective_on (physical_avoids_three f hc a b hd.1) (physical_avoids_three f hc a d hd.2.1) hm.1,
  threeIndex_injective_on (physical_avoids_three f hc a d hd.2.1) (physical_avoids_three f hc b d hd.2.2) hm.2⟩

theorem restored_foreign {k : Bool} {c : Host} (f : Physical45 k c) :
 ForeignCanonical k (restoredColoring f) := by
 refine ⟨?_,?_⟩
 · intro i hi
   change threeIndex (c (f.physical 14) (f.physical i))=_
   rw [f.root_edges i hi]
   exact threeIndex_palette _
 · intro a b hab ha hb hz hg
   change threeIndex (c (f.physical a) (f.physical b))=_
   rw [f.foreign_edges a b hab ha hb hz hg]
   exact threeIndex_palette _

theorem physical_reordering_preserves_foreign {k : Bool} {c : Host} (f : Physical45 k c)
 (p : Equiv.Perm (Fin 5)) (i : Fin 15) (hi : 5 ≤ i.val) :
 f.physical (OwnFive15.freeLift p i)=f.physical i := by rw [OwnFive15.freeLift_ge5 p i hi]
#print axioms restored_good
end PricingC.Rooted45Orientation
