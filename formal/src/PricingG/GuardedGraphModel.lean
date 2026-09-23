import PricingG.GuardedCenters
import PricingG.StarPentagonTransport

namespace PricingG
open Finset Ramsey61

/-- The entire shared-graph reduction retains both physical neighborhood
embeddings and both fixed palettes as part of its data. -/
structure GuardedGraphModel (c : Host) (r : Fin 61) (p q : FourColor) (hpq : p ≠ q) where
  X : PhysicalBlock c r p
  Y : PhysicalBlock c r q
  f : Equiv.Perm (Fin 16)
  g : Equiv.Perm (Fin 16)
  first_fiber : ∀ x y, (X.graph q hpq.symm).Adj (f y) x ↔
    c (X.map.vertex x) (Y.map.vertex y) = q
  second_fiber : ∀ x y, (Y.graph p hpq).Adj (g x) y ↔
    c (X.map.vertex x) (Y.map.vertex y) = p

namespace GuardedGraphModel
noncomputable def K {c r p q hpq} (m : GuardedGraphModel c r p q hpq) := m.X.graph q hpq.symm
noncomputable instance Kdec {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : DecidableRel m.K.Adj :=
  PhysicalBlock.graph_decidable _ _ _

noncomputable def J {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : SimpleGraph (Fin 16) :=
  R4333.colorGraph (R4333.relabelVertices m.Y.model m.g) (m.Y.selectedColor p hpq)
noncomputable instance Jdec {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : DecidableRel m.J.Adj :=
  R4333.colorGraphDecidableRel _ _

noncomputable def imageRule {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : Equiv.Perm (Fin 16) :=
  m.g.trans m.f

theorem K_srg {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : m.K.IsSRGWith 16 5 0 2 :=
  m.X.graph_srg q hpq.symm

theorem J_srg {c r p q hpq} (m : GuardedGraphModel c r p q hpq) : m.J.IsSRGWith 16 5 0 2 :=
  R4333.k16_colorGraph_isSRG _ (R4333.noMono_relabelVertices _ _ m.Y.good) _

theorem J_iff {c r p q hpq} (m : GuardedGraphModel c r p q hpq) (x y : Fin 16) :
    m.J.Adj x y ↔ (m.Y.graph p hpq).Adj (m.g x) (m.g y) := by
  change (x ≠ y ∧ m.Y.model (m.g x) (m.g y) = _) ↔
    (m.g x ≠ m.g y ∧ m.Y.model (m.g x) (m.g y) = _)
  exact and_congr_left fun _ => m.g.injective.ne_iff.symm

theorem J_physical_iff {c r p q hpq} (m : GuardedGraphModel c r p q hpq) (x y : Fin 16) :
    m.J.Adj x y ↔ c (m.X.map.vertex x) (m.Y.map.vertex (m.g y)) = p := by
  rw [m.J_iff,m.second_fiber]

/-- Each shared J-neighborhood is a star or a rooted pentagon in K, with
its exact center/zero-neighbor tied to the actual physical center permutation. -/
theorem shared_graph_rooted_dichotomy {c r p q hpq}
    (m : GuardedGraphModel c r p q hpq) (hc : NoMonochromaticTriangle c)
    (hG : RegularOverlapGuard c r p q) (y : Fin 16) :
    (∃ a, m.K.Adj (m.imageRule y) a ∧ m.J.neighborFinset y = m.K.neighborFinset a) ∨
    (InducedDegreeTwo m.K (m.J.neighborFinset y) ∧
      RootPentagonLaw m.K (m.imageRule y) (m.J.neighborFinset y)) := by
  classical
  let A := m.J.neighborFinset y
  have hA : A.card = 5 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact m.J_srg.regular y
  have havoid : Disjoint A (m.K.neighborFinset (m.imageRule y)) := by
    apply disjoint_left.mpr
    intro x hx hk
    have hp := (m.J_physical_iff x y).mp
      ((m.J.adj_comm y x).mp ((m.J.mem_neighborFinset y x).mp hx))
    have hq := (m.first_fiber x (m.g y)).mp ((m.K.mem_neighborFinset _ _).mp hk)
    exact hpq (hp.symm.trans hq)
  have hmask : RootMaskCondition m.K (m.imageRule y) A := by
    intro x hx
    have hcross := (m.first_fiber x (m.g y)).mp ((m.K.mem_neighborFinset _ _).mp hx)
    have hm := physical_block_mask m.X m.Y hc hpq x (m.g y)
      (hG.first_opposite_high _ (m.X.map.mem_neighborhood x)) hcross
    have heq : (A.filter fun a => m.K.Adj x a) =
      (m.K.neighborFinset x).filter fun a =>
        c (m.X.map.vertex a) (m.Y.map.vertex (m.g y)) = p := by
      ext a
      simp only [A,mem_filter,SimpleGraph.mem_neighborFinset]
      rw [m.J.adj_comm y a,m.J_physical_iff]
      exact and_comm
    rwa [heq]
  exact rooted_star_or_pentagon m.K m.K_srg (m.imageRule y) A hA havoid hmask
end GuardedGraphModel

/-- Construct the shared graph data from the original guarded host alone. -/
theorem regular_overlap_has_graph_model
    (c : Host) (hc : NoMonochromaticTriangle c) (r : Fin 61) (p q : FourColor)
    (hG : RegularOverlapGuard c r p q) :
    Nonempty (GuardedGraphModel c r p q hG.colors_distinct) := by
  obtain ⟨X,Y,f,g,hf,hg,hF,hG'⟩ := regular_overlap_has_bijective_centers c hc r p q hG
  exact ⟨⟨X,Y,Equiv.ofBijective f hf,Equiv.ofBijective g hg,hF,hG'⟩⟩

#print axioms regular_overlap_has_graph_model
#print axioms GuardedGraphModel.shared_graph_rooted_dichotomy
end PricingG
