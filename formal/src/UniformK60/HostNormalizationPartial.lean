import UniformK60.HostNormalization
import Mathlib.Logic.Equiv.Fintype

set_option autoImplicit false
namespace UniformK60.HostNormalization
open Ramsey61 UniformK60.Physical

/-- A finite injective placement preserving root-cell labels extends to one
permutation of the whole host preserving every label. Complete templates and
partial low supports may be supplied together; all complements are filled
inside their actual cells. -/
theorem extend_partial_label_preserving {A B : Type*} [Finite A]
    (label : Vertex → B) (source target : A ↪ Vertex)
    (hlabel : ∀ a, label (target a) = label (source a)) :
    ∃ e : Vertex ≃ Vertex, (∀ a, e (source a) = target a) ∧
      ∀ v, label (e v) = label v := by
  classical
  have each (b : B) :
      ∃ e : Equiv.Perm {v // label v = b},
        ∀ a : {a // label (source a) = b},
          e ⟨source a.val, a.property⟩ =
            ⟨target a.val, (hlabel a.val).trans a.property⟩ := by
    let f : {a // label (source a) = b} → {v // label v = b} :=
      fun a => ⟨source a.val, a.property⟩
    let g : {a // label (source a) = b} → {v // label v = b} :=
      fun a => ⟨target a.val, (hlabel a.val).trans a.property⟩
    have hf : Function.Injective f := by
      intro a a' h
      apply Subtype.ext
      exact source.injective (congrArg (fun v : {v // label v = b} => v.val) h)
    have hg : Function.Injective g := by
      intro a a' h
      apply Subtype.ext
      exact target.injective (congrArg (fun v : {v // label v = b} => v.val) h)
    exact Equiv.Perm.exists_extending_pair f g hf hg
  choose es hes using each
  refine ⟨Equiv.ofFiberEquiv es, ?_, Equiv.ofFiberEquiv_map es⟩
  intro a
  change (es (label (source a)) ⟨source a, rfl⟩).val = target a
  exact congrArg Subtype.val (hes (label (source a)) ⟨a, rfl⟩)

/-- Including the root among the prescribed points fixes it in the same
whole-host extension used by the supports and both foreign templates. -/
theorem extend_partial_root_map {A B : Type*} [Finite A]
    (label : Vertex → B) (source target : A ↪ Vertex)
    (hlabel : ∀ a, label (target a) = label (source a))
    (a0 : A) (hs0 : source a0 = 0) (ht0 : target a0 = 0) :
    ∃ e : Vertex ≃ Vertex, e 0 = 0 ∧ (∀ a, e (source a) = target a) ∧
      ∀ v, label (e v) = label v := by
  obtain ⟨e, he, hl⟩ := extend_partial_label_preserving label source target hlabel
  refine ⟨e, ?_, he, hl⟩
  simpa only [hs0, ht0] using he a0

#print axioms extend_partial_label_preserving
#print axioms extend_partial_root_map
end UniformK60.HostNormalization
