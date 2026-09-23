import PricingABD.ABGeometry
import R4333Lean.ProfileDFourRowCNF
import R4333Lean.ProfileDHighOwnFiveSupportC5CNF

set_option autoImplicit false
namespace PricingIntegration.DFrameColoring
open Ramsey61
open Ramsey61.CEncodingCore (palette palette_injective palette_surjective)
open PricingABD PricingABD.ABLayout PricingABD.ABGeometry
open R4333.ProfileDTripleJoinReduction

def layout (five : Bool) : Layout := ⟨.D,five⟩
def kind (t : Types) : Kind := Kind.ofBooleans t.left t.right t.marked

noncomputable def paletteEquiv : Fin 4 ≃ FourColor := Equiv.ofBijective palette
  ⟨palette_injective,palette_surjective⟩

noncomputable def coloring {c : Host} {five : Bool} (f : Frame c (layout five)) :
    R4333.EdgeColoring (Fin (vertexCount (layout five))) (Fin 4) where
  color u v:=paletteEquiv.symm (c (f.vertex u) (f.vertex v))
  color_symm u v:=congrArg paletteEquiv.symm (c.color_symm _ _)

theorem coloring_good {c : Host} {five : Bool} (f : Frame c (layout five))
    (hc : NoMonochromaticTriangle c) : R4333.NoMonochromaticTriangle (coloring f) := by
  intro u v w hd hm
  exact hc (f.vertex u) (f.vertex v) (f.vertex w)
    ⟨f.vertex.injective.ne hd.1,f.vertex.injective.ne hd.2.1,f.vertex.injective.ne hd.2.2⟩
    ⟨paletteEquiv.symm.injective hm.1,paletteEquiv.symm.injective hm.2⟩

def tailIndex (five : Bool) (i : Fin 46) : Fin (vertexCount (layout five)) := ABLayout.tail (layout five) i

theorem tailIndex_injective (five : Bool) : Function.Injective (tailIndex five) :=
  tail_injective (layout five)

@[simp] theorem tailIndex_left (five : Bool) (i : Fin 15) :
    tailIndex five (blockVertex 0 i.val)=ABLayout.left (layout five) i := by
  apply Fin.ext
  rw [show (tailIndex five (blockVertex 0 i.val)).val=freeSize (layout five)+(blockVertex 0 i.val).val from rfl]
  rw [blockVertex_val 0 (show i.val<blockSize 0 from i.isLt)]
  simp [ABLayout.left,leftStart,blockStart]

@[simp] theorem tailIndex_right (five : Bool) (i : Fin 15) :
    tailIndex five (blockVertex 1 i.val)=ABLayout.right (layout five) i := by
  apply Fin.ext
  rw [show (tailIndex five (blockVertex 1 i.val)).val=freeSize (layout five)+(blockVertex 1 i.val).val from rfl]
  rw [blockVertex_val 1 (show i.val<blockSize 1 from i.isLt)]
  simp [ABLayout.right,rightStart,blockStart,leftSize,leftLarge,layout]
  omega

@[simp] theorem tailIndex_marked (five : Bool) (i : Fin 16) :
    tailIndex five (blockVertex 2 i.val)=ABLayout.marked (layout five) i := by
  apply Fin.ext
  rw [show (tailIndex five (blockVertex 2 i.val)).val=freeSize (layout five)+(blockVertex 2 i.val).val from rfl]
  rw [blockVertex_val 2 (show i.val<blockSize 2 from i.isLt)]
  simp [ABLayout.marked,markedStart,blockStart,leftSize,leftLarge,rightSize,rightLarge,layout]
  omega

theorem foreign_eq_canonical (own : Fin 4) (q : Fin 3) :
    foreign own q=R4333.SingleRootStarCNF.canonicalPalette own q := by
  fin_cases own <;> fin_cases q <;> rfl

theorem coloring_left {c : Host} {five : Bool} (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (u v : Fin 15) (hne : u≠v) :
    coloring f (ABLayout.left (layout five) u) (ABLayout.left (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 1 (R4333.k15Template t.left u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c (f.vertex (ABLayout.left (layout five) u)) (f.vertex (ABLayout.left (layout five) v)) =
    palette (R4333.SingleRootStarCNF.canonicalPalette 1 (R4333.k15Template t.left u v))
  have h : c (f.vertex (ABLayout.left (layout five) u)) (f.vertex (ABLayout.left (layout five) v)) =
    palette (foreign 1 (R4333.k15Template t.left u v)) := hg.left u v hne
  simpa only [foreign_eq_canonical] using h

theorem coloring_right {c : Host} {five : Bool} (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (u v : Fin 15) (hne : u≠v) :
    coloring f (ABLayout.right (layout five) u) (ABLayout.right (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 2 (R4333.k15Template t.right u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c (f.vertex (ABLayout.right (layout five) u)) (f.vertex (ABLayout.right (layout five) v)) =
    palette (R4333.SingleRootStarCNF.canonicalPalette 2 (R4333.k15Template t.right u v))
  have h : c (f.vertex (ABLayout.right (layout five) u)) (f.vertex (ABLayout.right (layout five) v)) =
    palette (foreign 2 (R4333.k15Template t.right u v)) := hg.right u v hne
  simpa only [foreign_eq_canonical] using h

theorem coloring_marked {c : Host} {five : Bool} (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (u v : Fin 16) (hne : u≠v) :
    coloring f (ABLayout.marked (layout five) u) (ABLayout.marked (layout five) v)=
      R4333.SingleRootStarCNF.canonicalPalette 3 (R4333.k16Template t.marked u v) := by
  apply (Equiv.symm_apply_eq paletteEquiv).mpr
  change c (f.vertex (ABLayout.marked (layout five) u)) (f.vertex (ABLayout.marked (layout five) v)) =
    palette (R4333.SingleRootStarCNF.canonicalPalette 3 (R4333.k16Template t.marked u v))
  simpa only [foreign_eq_canonical] using hg.marked u v hne

noncomputable def tailColoring {c : Host} {five : Bool} (f : Frame c (layout five)) :=
  R4333.pullbackColoring (coloring f) (tailIndex five)

theorem tail_templates {c : Host} {five : Bool} (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (block : Fin 3) (a b : Nat)
    (ha : a<blockSize block) (hb : b<blockSize block) (hab : a<b) :
    tailColoring f (blockVertex block a) (blockVertex block b)=
      R4333.SingleRootStarCNF.canonicalPalette (Fin.succ block)
        (R4333.SingleRootStarCNF.templateColor (blockSize block) ((kind t).twisted block) a b) := by
  fin_cases block
  · let u : Fin 15:=⟨a,ha⟩
    let v : Fin 15:=⟨b,hb⟩
    have h:=coloring_left f t hg u v (Fin.ne_of_lt hab)
    change coloring f (tailIndex five (blockVertex 0 u.val)) (tailIndex five (blockVertex 0 v.val)) = _
    rw [tailIndex_left,tailIndex_left]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring f (ABLayout.left (layout five) u) (ABLayout.left (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 1 (R4333.k15Template t.left ⟨a%15,by omega⟩ ⟨b%15,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<15 from ha),Nat.mod_eq_of_lt (show b<15 from hb)] using h
  · let u : Fin 15:=⟨a,ha⟩
    let v : Fin 15:=⟨b,hb⟩
    have h:=coloring_right f t hg u v (Fin.ne_of_lt hab)
    change coloring f (tailIndex five (blockVertex 1 u.val)) (tailIndex five (blockVertex 1 v.val)) = _
    rw [tailIndex_right,tailIndex_right]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring f (ABLayout.right (layout five) u) (ABLayout.right (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 2 (R4333.k15Template t.right ⟨a%15,by omega⟩ ⟨b%15,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<15 from ha),Nat.mod_eq_of_lt (show b<15 from hb)] using h
  · let u : Fin 16:=⟨a,ha⟩
    let v : Fin 16:=⟨b,hb⟩
    have h:=coloring_marked f t hg u v (Fin.ne_of_lt hab)
    change coloring f (tailIndex five (blockVertex 2 u.val)) (tailIndex five (blockVertex 2 v.val)) = _
    rw [tailIndex_marked,tailIndex_marked]
    simp only [kind,Kind.twisted_ofBooleans]
    change coloring f (ABLayout.marked (layout five) u) (ABLayout.marked (layout five) v) =
      R4333.SingleRootStarCNF.canonicalPalette 3 (R4333.k16Template t.marked ⟨a%16,by omega⟩ ⟨b%16,by omega⟩)
    simpa only [Nat.mod_eq_of_lt (show a<16 from ha),Nat.mod_eq_of_lt (show b<16 from hb)] using h

noncomputable def witness {c : Host} {five : Bool} (f : Frame c (layout five))
    (t : Types) (hg : Geometry t f) (hc : NoMonochromaticTriangle c) : Witness (kind t) where
  coloring:=tailColoring f
  noMono:=R4333.noMono_pullback (coloring f) (tailIndex five) (tailIndex_injective five) (coloring_good f hc)
  templateCanonical:=tail_templates f t hg

#print axioms witness
end PricingIntegration.DFrameColoring
