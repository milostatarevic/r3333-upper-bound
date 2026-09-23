import PricingC.OwnFive15

namespace PricingC.Rooted45Orientation
open R4333

/-- false is545; true is554. The free block always has five vertices. -/
def boundary (k : Bool) : Nat := if k then 10 else 9

def group (k : Bool) (i : Fin 15) : ThreeColor :=
 if i.val < 5 then 0 else if i.val < boundary k then 1 else 2

def Cycle (n a b : Nat) : Prop :=
 a+1=b ∨ b+1=a ∨ (n=5 ∧ ((a=0 ∧ b=4) ∨ (a=4 ∧ b=0)))
instance (n a b : Nat) : Decidable (Cycle n a b) := by unfold Cycle;infer_instance

def interior (k : Bool) (a b : Fin 15) : ThreeColor :=
 if a.val < 5 then (if Cycle 5 a.val b.val then 1 else 2)
 else if a.val < boundary k then
  (if Cycle (if k then 5 else 4) (a.val-5) (b.val-5) then 0 else 2)
 else (if Cycle (if k then 4 else 5) (a.val-boundary k) (b.val-boundary k) then 0 else 1)

structure Canonical (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor) : Prop where
 root_edges : ∀ i,i≠14 → c 14 i=group k i
 block_edges : ∀ a b,a≠b → a≠14 → b≠14 → group k a=group k b → c a b=interior k a b

structure ForeignCanonical (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor) : Prop where
 root_edges : ∀ i,i≠14 → c 14 i=group k i
 foreign_edges : ∀ a b,a≠b → a≠14 → b≠14 → group k a≠0 → group k a=group k b → c a b=interior k a b

def vertexMap (k : Bool) : Fin 15 → Fin 15 :=
 if k then ![10,11,12,13,0,2,4,1,3,5,7,9,6,8,14]
 else ![5,6,7,8,0,1,2,3,4,9,11,13,10,12,14]
def vertexInv (k : Bool) : Fin 15 → Fin 15 :=
 if k then ![4,7,5,8,6,9,12,10,13,11,0,1,2,3,14]
 else ![4,5,6,7,8,0,1,2,3,9,12,10,13,11,14]

private theorem vertex_left : ∀ k,Function.LeftInverse (vertexInv k) (vertexMap k) := by decide
private theorem vertex_right : ∀ k,Function.RightInverse (vertexInv k) (vertexMap k) := by decide

def vertices (k : Bool) : Equiv.Perm (Fin 15) :=
 ⟨vertexMap k,vertexInv k,vertex_left k,vertex_right k⟩

def colorMap (k : Bool) : ThreeColor → ThreeColor :=
 if k then ![1,2,0] else ![1,0,2]
def colorInv (k : Bool) : ThreeColor → ThreeColor :=
 if k then ![2,0,1] else ![1,0,2]
def colors (k : Bool) : Equiv.Perm ThreeColor where
 toFun := colorMap k
 invFun := colorInv k
 left_inv := by cases k <;> decide
 right_inv := by cases k <;> decide

def transport (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor) : EdgeColoring (Fin 15) ThreeColor :=
 mapEdgeColors (relabelVertices c (vertices k)) (colors k)

theorem transport_good (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor)
 (hc : NoMonochromaticTriangle c) : NoMonochromaticTriangle (transport k c) :=
 noMono_mapEdgeColors _ _ (noMono_relabelVertices _ _ hc)

theorem vertices_root : ∀ k,vertices k 14=14 := by decide

theorem vertices_ne_root (k : Bool) (a : Fin 15) (ha:a≠14) : vertices k a≠14 := by
 intro h
 exact ha ((vertices k).injective (h.trans (vertices_root k).symm))

set_option maxRecDepth 100000 in
theorem root_groups : ∀ k : Bool,∀ i : Fin 15,i≠14 →
 colors k (group k (vertices k i))=PricingABD.Rooted455Entrance.group i := by decide

set_option maxRecDepth 100000 in
theorem zero_same_group : ∀ k : Bool,∀ i j : Fin 4,
 group k (vertices k (PricingABD.Rooted455Entrance.label0 i))=
 group k (vertices k (PricingABD.Rooted455Entrance.label0 j)) := by decide
set_option maxRecDepth 100000 in
theorem one_same_group : ∀ k : Bool,∀ i j : Fin 5,
 group k (vertices k (PricingABD.Rooted455Entrance.label1 i))=
 group k (vertices k (PricingABD.Rooted455Entrance.label1 j)) := by decide
set_option maxRecDepth 100000 in
theorem two_same_group : ∀ k : Bool,∀ i j : Fin 5,
 group k (vertices k (PricingABD.Rooted455Entrance.label2 i))=
 group k (vertices k (PricingABD.Rooted455Entrance.label2 j)) := by decide

set_option maxRecDepth 100000 in
theorem zero_colors : ∀ k : Bool,∀ i j : Fin 4,i≠j →
 colors k (interior k (vertices k (PricingABD.Rooted455Entrance.label0 i))
  (vertices k (PricingABD.Rooted455Entrance.label0 j)))=PricingABD.Rooted455Data.canonical0 i j := by decide
set_option maxRecDepth 100000 in
theorem one_colors : ∀ k : Bool,∀ i j : Fin 5,i≠j →
 colors k (interior k (vertices k (PricingABD.Rooted455Entrance.label1 i))
  (vertices k (PricingABD.Rooted455Entrance.label1 j)))=PricingABD.Rooted455Data.canonical1 i j := by decide
set_option maxRecDepth 100000 in
theorem two_colors : ∀ k : Bool,∀ i j : Fin 5,i≠j →
 colors k (interior k (vertices k (PricingABD.Rooted455Entrance.label2 i))
  (vertices k (PricingABD.Rooted455Entrance.label2 j)))=PricingABD.Rooted455Data.canonical2 i j := by decide

/-- One exact coordinate/palette recoding gives the proved455 catalogue.
The final word transport will undo this recoding on every physical edge. -/
theorem transport_canonical (k : Bool) (c : EdgeColoring (Fin 15) ThreeColor)
 (h : Canonical k c) : PricingABD.Rooted455Entrance.CanonicalRooted455 (transport k c) := by
 refine ⟨?_,?_,?_,?_⟩
 · intro i hi
   change colors k (c (vertices k 14) (vertices k i))=_
   rw [vertices_root,h.root_edges _ (vertices_ne_root k i hi)]
   exact root_groups k i hi
 · intro i j hij
   change colors k (c (vertices k (PricingABD.Rooted455Entrance.label0 i))
    (vertices k (PricingABD.Rooted455Entrance.label0 j)))=_
   rw [h.block_edges _ _ ((vertices k).injective.ne (PricingABD.Rooted455Entrance.label0_injective.ne hij))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label0_ne_root i))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label0_ne_root j)) (zero_same_group k i j)]
   exact zero_colors k i j hij
 · intro i j hij
   change colors k (c (vertices k (PricingABD.Rooted455Entrance.label1 i))
    (vertices k (PricingABD.Rooted455Entrance.label1 j)))=_
   rw [h.block_edges _ _ ((vertices k).injective.ne (PricingABD.Rooted455Entrance.label1_injective.ne hij))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label1_ne_root i))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label1_ne_root j)) (one_same_group k i j)]
   exact one_colors k i j hij
 · intro i j hij
   change colors k (c (vertices k (PricingABD.Rooted455Entrance.label2 i))
    (vertices k (PricingABD.Rooted455Entrance.label2 j)))=_
   rw [h.block_edges _ _ ((vertices k).injective.ne (PricingABD.Rooted455Entrance.label2_injective.ne hij))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label2_ne_root i))
    (vertices_ne_root k _ (PricingABD.Rooted455Entrance.label2_ne_root j)) (two_same_group k i j)]
   exact two_colors k i j hij

#print axioms transport_canonical
end PricingC.Rooted45Orientation
