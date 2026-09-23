import PricingABD.ABGeometry
import PricingABD.ABPosition

set_option autoImplicit false
namespace PricingABD.ABFixedColor
open Ramsey61 Ramsey61.CEncodingCore PricingABD.ABLayout PricingABD.ABGeometry PricingABD.ABPosition

def positionColor {l : Layout} (t : Types) : Position l → Position l → Option (Fin 4)
  | .free u, .free v => if u=v then none else some (freeColor l u v)
  | .left u, .left v => if u=v then none else some (foreign 1 (model (leftLarge l) t.left u v))
  | .right u, .right v => if u=v then none else some (foreign 2 (model (rightLarge l) t.right u v))
  | .marked u, .marked v => if u=v then none else some (foreign 3 (R4333.k16Template t.marked u v))
  | .free _, .marked v => if v=15 then some 3 else none
  | .marked u, .free _ => if u=15 then some 3 else none
  | _, _ => none

def fixedColor (l : Layout) (t : Types) (u v : Fin (vertexCount l)) : Option (Fin 4) :=
  positionColor t (decode l u) (decode l v)

@[simp] theorem fixedColor_encode {l : Layout} (t : Types) (u v : Position l) :
    fixedColor l t (encode u) (encode v)=positionColor t u v := by
  simp [fixedColor]

theorem offdiagonal_symm {α : Type} [DecidableEq α] (g : α → α → Fin 4)
    (hg : ∀u v,g u v=g v u) (u v : α) :
    (if u=v then none else some (g u v))=(if v=u then none else some (g v u)) := by
  by_cases h : u=v
  · subst v;simp
  · rw [if_neg h,if_neg (Ne.symm h),hg]

theorem positionColor_symm {l : Layout} (t : Types) (u v : Position l) :
    positionColor t u v=positionColor t v u := by
  cases u <;> cases v <;> try rfl
  · exact offdiagonal_symm (freeColor l) (freeColor_symm l) _ _
  · exact offdiagonal_symm _ (fun a b=>congrArg (foreign 1) ((model (leftLarge l) t.left).color_symm a b)) _ _
  · exact offdiagonal_symm _ (fun a b=>congrArg (foreign 2) ((model (rightLarge l) t.right).color_symm a b)) _ _
  · exact offdiagonal_symm _ (fun a b=>congrArg (foreign 3) ((R4333.k16Template t.marked).color_symm a b)) _ _

theorem fixedColor_symm (l : Layout) (t : Types) (u v : Fin (vertexCount l)) :
    fixedColor l t u v=fixedColor l t v u := positionColor_symm _ _ _

@[simp] theorem positionColor_diag {l : Layout} (t : Types) (u : Position l) :
    positionColor t u u=none := by cases u <;> simp [positionColor]
@[simp] theorem fixedColor_diag (l : Layout) (t : Types) (u : Fin (vertexCount l)) :
    fixedColor l t u u=none := positionColor_diag _ _

theorem domain_independent {l : Layout} (s t : Types) (u v : Position l) :
    (positionColor s u v).isNone=(positionColor t u v).isNone := by
  cases u <;> cases v <;> simp only [positionColor] <;> split_ifs <;> rfl

theorem fixed_domain_independent (l : Layout) (s t : Types) (u v : Fin (vertexCount l)) :
    (fixedColor l s u v).isNone=(fixedColor l t u v).isNone := domain_independent _ _ _ _

theorem position_sound {c : Host} {l : Layout} {t : Types} (f : Frame c l)
    (hg : Geometry t f) (u v : Position l) (q : Fin 4)
    (h : positionColor t u v=some q) : c (f.vertex (encode u)) (f.vertex (encode v))=palette q := by
  cases u with
  | free a =>
    cases v with
    | free b =>
      by_cases he : a=b
      · simp [positionColor,he] at h
      · simp only [positionColor,if_neg he] at h
        rw [←Option.some.inj h]
        exact hg.free a b he
    | left b => contradiction
    | right b => contradiction
    | marked b =>
      by_cases he : b=15
      · subst b
        simp only [positionColor,if_pos rfl] at h
        rw [←Option.some.inj h,c.color_symm]
        exact hg.mark_free a
      · simp [positionColor,he] at h
  | left a =>
    cases v with
    | free b => contradiction
    | left b =>
      by_cases he : a=b
      · simp [positionColor,he] at h
      · simp only [positionColor,if_neg he] at h
        rw [←Option.some.inj h]
        exact hg.left a b he
    | right b => contradiction
    | marked b => contradiction
  | right a =>
    cases v with
    | free b => contradiction
    | left b => contradiction
    | right b =>
      by_cases he : a=b
      · simp [positionColor,he] at h
      · simp only [positionColor,if_neg he] at h
        rw [←Option.some.inj h]
        exact hg.right a b he
    | marked b => contradiction
  | marked a =>
    cases v with
    | free b =>
      by_cases he : a=15
      · subst a
        simp only [positionColor,if_pos rfl] at h
        rw [←Option.some.inj h]
        exact hg.mark_free b
      · simp [positionColor,he] at h
    | left b => contradiction
    | right b => contradiction
    | marked b =>
      by_cases he : a=b
      · simp [positionColor,he] at h
      · simp only [positionColor,if_neg he] at h
        rw [←Option.some.inj h]
        exact hg.marked a b he

theorem fixed_sound {c : Host} {l : Layout} {t : Types} (f : Frame c l)
    (hg : Geometry t f) (u v : Fin (vertexCount l)) (q : Fin 4)
    (h : fixedColor l t u v=some q) : c (f.vertex u) (f.vertex v)=palette q := by
  simpa using position_sound f hg (decode l u) (decode l v) q h

#print axioms fixed_sound
#print axioms fixed_domain_independent
end PricingABD.ABFixedColor
