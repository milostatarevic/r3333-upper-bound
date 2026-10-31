import UniformK60.BalancedHost

/-! Exact 4/5-support selector lists, ordered first by size and then
lexicographically as in the independent input generator. -/
set_option autoImplicit false
namespace UniformK60.BalancedAnchor
open Ramsey61 UniformK61.BalancedEncodingData

def supportMasks : Array (Array (Array Nat)) := #[
  #[
    #[149, 533, 101, 2085, 2117, 645, 89, 8217, 169, 16425, 8265, 16521, 8273, 657, 2145, 16545, 10753, 18945, 25089, 26625, 86, 32790, 166, 4134, 32838, 4230, 154, 1050, 106, 298, 330, 1162, 32850, 1170, 354, 4258, 5378, 34050, 37122, 37890, 32852, 660, 2148, 4260, 6660, 35332, 37380, 38916, 8280, 1176, 360, 16552, 9480, 17672, 24840, 25608, 9744, 34320, 41488, 42000, 6432, 18720, 20768, 22560, 10560, 35136, 41280, 43072, 5760, 18048, 21120, 21632, 38144, 25856, 22784, 43264, 22016, 42496, 39424, 27136, 661, 2149, 8281, 16553, 27137, 32854, 4262, 1178, 362, 38146, 39428, 25864, 42512, 22816, 43328, 22144],
    #[85, 149, 533, 101, 165, 2085, 2117, 645, 89, 8217, 169, 16425, 8265, 16521, 8273, 657, 2145, 16545, 18465, 10305, 10753, 18945, 25089, 26625, 86, 32790, 166, 4134, 32838, 4230, 90, 154, 1050, 106, 170, 298, 330, 1162, 32850, 1170, 33810, 354, 4258, 5250, 5378, 34050, 37122, 37890, 32852, 660, 33300, 2148, 4260, 4740, 6660, 35332, 37380, 38916, 8280, 1176, 360, 16552, 16680, 8520, 9480, 17672, 24840, 25608, 9744, 34320, 41488, 42000, 6432, 18720, 20768, 22560, 10560, 35136, 41280, 43072, 5760, 18048, 21120, 21632, 21760, 38144, 25856, 42240, 22784, 43264, 22016, 42496, 23040, 39424, 27136, 43520, 661, 2149, 8281, 16553, 27137, 32854, 4262, 1178, 362, 38146, 39428, 25864, 42512, 22816, 43328, 22144]
  ],
  #[
    #[149, 533, 101, 2085, 2117, 645, 89, 8217, 169, 16425, 8265, 16521, 8273, 657, 2145, 16545, 10753, 18945, 25089, 26625, 86, 166, 4134, 4230, 154, 1050, 106, 298, 330, 1162, 1170, 354, 4258, 5378, 660, 2148, 4260, 6660, 8280, 1176, 360, 16552, 9480, 17672, 24840, 25608, 9744, 6432, 18720, 20768, 22560, 10560, 5760, 18048, 21120, 21632, 25856, 22784, 22016, 27136, 661, 2149, 8281, 16553, 27137, 4262, 1178, 362, 25864, 22816, 22144],
    #[85, 149, 533, 101, 165, 2085, 2117, 645, 89, 8217, 169, 16425, 8265, 16521, 8273, 657, 2145, 16545, 18465, 10305, 10753, 18945, 25089, 26625, 86, 166, 4134, 4230, 90, 154, 1050, 106, 170, 298, 330, 1162, 1170, 354, 4258, 5250, 5378, 660, 2148, 4260, 4740, 6660, 8280, 1176, 360, 16552, 16680, 8520, 9480, 17672, 24840, 25608, 9744, 6432, 18720, 20768, 22560, 10560, 5760, 18048, 21120, 21632, 21760, 25856, 22784, 22016, 23040, 27136, 661, 2149, 8281, 16553, 27137, 4262, 1178, 362, 25864, 22816, 22144]
  ]
]

def minorIndex (minor : Bool) : Nat := if minor then 1 else 0

def masks (minor kind : Bool) : Array Nat :=
  (supportMasks[minorIndex minor]!)[kindIndex kind]!

def maskSet (mask : Nat) : Finset (Fin 16) :=
  Finset.univ.filter fun v => mask.testBit v.val

abbrev PatternIndex (minor kind : Bool) := Fin (masks minor kind).size

def pattern (minor kind : Bool) (i : PatternIndex minor kind) : Finset (Fin 16) :=
  maskSet ((masks minor kind)[i.val]!)

def validPosition (minor : Bool) (v : Fin 16) : Prop := minor = false ∨ v.val < 15

instance (minor : Bool) (v : Fin 16) : Decidable (validPosition minor v) :=
  inferInstanceAs (Decidable (minor = false ∨ v.val < 15))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pattern_bounds : ∀ minor kind i, ∀ v ∈ pattern minor kind i,
    validPosition minor v := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pattern_counts :
    (masks false false).size = 96 ∧ (masks false true).size = 112 ∧
    (masks true false).size = 71 ∧ (masks true true).size = 83 := by decide +kernel

/- Every colored P4 in either full/minor literal template occurs in the
selector list. Successive edge tests prune invalid ordered tuples. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem p4_complete : ∀ (minor kind : Bool) (a : Fin 16), validPosition minor a →
    ∀ b : Fin 16, validPosition minor b → R4333.k16Template kind a b = 1 →
    ∀ d : Fin 16, validPosition minor d → R4333.k16Template kind a d = 2 →
      R4333.k16Template kind b d = 1 →
    ∀ e : Fin 16, validPosition minor e → R4333.k16Template kind a e = 2 →
      R4333.k16Template kind b e = 2 → R4333.k16Template kind d e = 1 →
    ∃ i : PatternIndex minor kind, pattern minor kind i = {a,b,d,e} := by decide +kernel

/- The proved complete sixteen-cycle list remains complete after restricting
to coordinates below15. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem c5_table_complete : ∀ (minor kind : Bool) (k : Fin 16),
    (∀ v ∈ UniformK61.BalancedEncodingData.support kind k, validPosition minor v) →
    ∃ i : PatternIndex minor kind,
      pattern minor kind i = UniformK61.BalancedEncodingData.support kind k := by decide +kernel

theorem c5_complete (minor kind : Bool) (s : Finset (Fin 16))
    (hs : s.card = 5) (hi : UniformK61.BalancedAnchor.Independent kind s)
    (hv : ∀ v ∈ s, validPosition minor v) :
    ∃ i : PatternIndex minor kind, pattern minor kind i = s := by
  obtain ⟨k,hk⟩ := UniformK61.BalancedAnchor.support_complete kind s hs hi
  rw [←hk] at hv ⊢
  exact c5_table_complete minor kind k hv

#print axioms p4_complete
#print axioms c5_complete
end UniformK60.BalancedAnchor
