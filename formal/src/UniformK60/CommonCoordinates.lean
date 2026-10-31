import UniformK60.CommonHost
import UniformK61.CommonHost

/-! Exact arithmetic correspondence between the archived61-position labels
and the physical60-position layout. These small finite identities do not
use any whole-host K61 hypothesis. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace UniformK60.CommonCoordinates
open UniformK60.Physical UniformK60.CommonHost
open PricingABD.ABLayout

namespace Reference
abbrev low := UniformK61.CommonHost.lowVertex
abbrev left := UniformK61.CommonHost.leftVertex
abbrev right := UniformK61.CommonHost.rightVertex
abbrev marked := UniformK61.CommonHost.markedVertex
end Reference

theorem deleted_root (l : Layout) (missing : Missing) :
    (omission l missing).predAbove (0 : Fin 61)=0 := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert missing <;> decide +kernel

theorem left_survives (l : Layout) (missing : Missing) (i : Fin (leftSize l)) :
    Reference.left l i≠(omission l missing).castSucc := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem right_survives (l : Layout) (missing : Missing) (i : Fin (rightSize l)) :
    Reference.right l i≠(omission l missing).castSucc := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem marked_survives (l : Layout) (missing : Missing) (i : Fin (markedSize missing)) :
    Reference.marked l (markedPosition missing i)≠(omission l missing).castSucc := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert missing <;> decide +kernel

theorem deleted_left (l : Layout) (missing : Missing) (i : Fin (leftSize l)) :
    (omission l missing).predAbove (Reference.left l i)=leftVertex l missing i := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem deleted_right (l : Layout) (missing : Missing) (i : Fin (rightSize l)) :
    (omission l missing).predAbove (Reference.right l i)=rightVertex l missing i := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem deleted_marked (l : Layout) (missing : Missing) (i : Fin (markedSize missing)) :
    (omission l missing).predAbove (Reference.marked l (markedPosition missing i))=
      markedVertex l missing i := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert missing <;> decide +kernel

theorem surviving_low_bound (l : Layout) (missing : Missing) (i : Fin (lowSize l))
    (hi : Reference.low l i≠(omission l missing).castSucc) : i.val<actualLow l missing := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

def lowIndex (l : Layout) (missing : Missing) (i : Fin (lowSize l))
    (hi : Reference.low l i≠(omission l missing).castSucc) : Fin (actualLow l missing) :=
  ⟨i.val,surviving_low_bound l missing i hi⟩

theorem deleted_low (l : Layout) (missing : Missing) (i : Fin (lowSize l))
    (hi : Reference.low l i≠(omission l missing).castSucc) :
    (omission l missing).predAbove (Reference.low l i)=lowVertex l missing (lowIndex l missing i hi) := by
  apply Fin.ext
  rw [UniformK60.UnitRestriction.restricted_position_value]
  have := sizes l
  have hbound := surviving_low_bound l missing i hi
  cases missing <;> simp only [omission,actualLow,Reference.low,UniformK61.CommonHost.lowVertex,
    lowVertex,lowIndex] at * <;> split_ifs <;> omega

theorem deleted_free (l : Layout) (missing : Missing) (i : Fin (freeSize l)) :
    (omission l missing).predAbove (UniformK61.CommonHost.retain l (PricingABD.ABLayout.free l i))=
      lowVertex l missing (Fin.castLE (free_le_low l missing) i) := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem marked_preimage (l : Layout) (missing : Missing) (i : Fin 16)
    (hi : Reference.marked l i≠(omission l missing).castSucc) :
    ∃ j : Fin (markedSize missing),markedPosition missing j=i := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert i missing <;> decide +kernel

theorem root_survives (l : Layout) (missing : Missing) :
    (0 : Fin 61)≠(omission l missing).castSucc := by
  rcases l with ⟨p,five⟩
  cases p <;> cases five <;> revert missing <;> decide +kernel

theorem mark_survives (l : Layout) (missing : Missing) :
    (60 : Fin 61)≠(omission l missing).castSucc := by
  intro h
  have := (omission l missing).isLt
  have hv : (60 : Nat)=(omission l missing).val := congrArg Fin.val h
  omega

theorem deleted_mark (l : Layout) (missing : Missing) :
    (omission l missing).predAbove (60 : Fin 61)=59 := by
  have := deleted_marked l missing (markIndex missing)
  rw [markedPosition_mark,markedVertex_mark] at this
  exact this

end UniformK60.CommonCoordinates
