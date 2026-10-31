import UniformK60.BalancedProjectedFinite
import UniformK60.NativeCatalogue

set_option autoImplicit false
namespace UniformK60.BalancedProjectedHost
open Ramsey61 UniformK60.Physical UniformK60.ThreeSupportFrame
open CompletionC.NativeMatrices UniformK60.NativeCatalogue
open UniformK60.BalancedProjectedData UniformK60.BalancedProjectedFinite

theorem group_active : ∀ s a, group s a≠3 ↔ a.val<s.dimension := by decide

theorem forward_active (g : Geometry) (i : Fin 600) (a : Fin 15) :
    (forward g i a).val<(geometryShape g).dimension ↔ a.val<(geometryShape g).dimension := by
  rw [← group_active, (structural g i).2.2.2.2.2.1, group_active]

theorem inverse_active (g : Geometry) (i : Fin 600) (a : Fin 15) :
    (inverse g i a).val<(geometryShape g).dimension ↔ a.val<(geometryShape g).dimension := by
  have h := forward_active g i (inverse g i a)
  rw [(structural g i).2.2.2.2.1] at h
  exact h.symm

def rowPadded (g : Geometry) (i : Fin 600)
    (a : Fin (rowShape (target g i)).dimension) : Fin 15 :=
  Fin.castLE (row_dimensions (target g i)).2.1 a

def nativeOfRow (g : Geometry) (i : Fin 600)
    (a : Fin (rowShape (target g i)).dimension) : Fin (geometryShape g).dimension :=
  ⟨(inverse g i (rowPadded g i a)).val, (inverse_active g i _).mpr (by
    change a.val<(geometryShape g).dimension
    rw [← (structural g i).1]
    exact a.isLt)⟩

theorem nativeOfRow_injective (g : Geometry) (i : Fin 600) :
    Function.Injective (nativeOfRow g i) := by
  intro a b h
  have hi : inverse g i (rowPadded g i a)=inverse g i (rowPadded g i b) :=
    Fin.ext (congrArg (fun x : Fin (geometryShape g).dimension => x.val) h)
  have hab : rowPadded g i a=rowPadded g i b := by
    have hf := congrArg (forward g i) hi
    simpa only [(structural g i).2.2.2.2.1] using hf
  exact Fin.ext (congrArg (fun x : Fin 15 => x.val) hab)

noncomputable def rowEmbedding {c : Host} (g : Geometry)
    (f : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right)
    (p : Equiv.Perm (Fin (geometryShape g).free)) (i : Fin 600) :
    Fin (rowShape (target g i)).dimension ↪ Vertex :=
  ⟨fun a => reorderedVertex (geometryShape g) f p (nativeOfRow g i a),
    (reorderedVertex (geometryShape g) f p).injective.comp (nativeOfRow_injective g i)⟩

/-- Every native physical brace has a row-indexed realization of one projected
row. Its real support moves by the certified full-template equivalence. -/
theorem actual_projected_cover {c : Host} (g : Geometry)
    (f : Frame c (geometryShape g).free (geometryShape g).left (geometryShape g).right)
    (hc : NoMonochromaticTriangle c) :
    ∃ p : Equiv.Perm (Fin (geometryShape g).free), ∃ i : Fin 600,
      Structural g i ∧
      ∀ a b : Fin (rowShape (target g i)).dimension,a≠b →
        c (rowEmbedding g f p i a) (rowEmbedding g f p i b)=
          palette (rowMatrix (target g i) (rowPadded g i a) (rowPadded g i b)) := by
  obtain ⟨p,i,he⟩ := actual_catalogue (geometryShape g) f hc
  refine ⟨p,i,structural g i,?_⟩
  intro a b hab
  have hne := (nativeOfRow_injective g i).ne hab
  have h := (he (nativeOfRow g i a) (nativeOfRow g i b) hne).trans
    (congrArg palette (matrix_transport g i _ _ hne))
  have ha : forward g i (Fin.castLE (geometry_dimensions g).2.1 (nativeOfRow g i a))=
      rowPadded g i a := (structural g i).2.2.2.2.1 _
  have hb : forward g i (Fin.castLE (geometry_dimensions g).2.1 (nativeOfRow g i b))=
      rowPadded g i b := (structural g i).2.2.2.2.1 _
  simpa only [ha,hb,rowEmbedding,Function.Embedding.coeFn_mk] using h

theorem realEquiv_preserves (g : Geometry) (i : Fin 600) (u v : Fin 16) (hne : u≠v) :
    R4333.k16Template (geometryKind g) (realEquiv g i u) (realEquiv g i v)=
      R4333.k16Template (geometryKind g) u v := by
  have h := fullAction_preserves (action g i) u v hne
  rw [(structural g i).2.2.1] at h
  exact h

#print axioms actual_projected_cover
end UniformK60.BalancedProjectedHost
