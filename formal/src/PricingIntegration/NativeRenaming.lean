import Std.Data.HashMap.Lemmas
import PricingABD.DenseSemantics
import Ramsey61.DenseCounter

set_option autoImplicit false
namespace PricingIntegration.NativeRenaming
open Ramsey61.DenseCounter

/-- A finite native variable table, extended injectively outside its range.
The inverse need not be injective: repeated entries would merely leave some
native variables unused. Every sparse atom still has a proved round trip. -/
def entries (size : Nat) (inverse : Nat → Nat) : List (Nat × Nat) :=
  (List.finRange (size-1)).map (fun i=>(inverse (i.val+1),i.val+1))

def forward (size : Nat) (inverse : Nat → Nat) : Std.HashMap Nat Nat :=
  (entries size inverse).foldl (fun m p=>m.insert p.1 p.2) ∅

def encode (size : Nat) (table : Std.HashMap Nat Nat) (a : Nat) : Nat :=
  match table[a]? with
  | some d=>d
  | none=>size+a

def decode (size : Nat) (inverse : Nat → Nat) (d : Nat) : Nat :=
  if d<size then inverse d else d-size

theorem fold_sound (P : Nat → Nat → Prop) (pairs : List (Nat × Nat))
    (m : Std.HashMap Nat Nat)
    (hm : ∀a d,m[a]?=some d → P a d)
    (hp : ∀p∈pairs,P p.1 p.2) :
    ∀a d,(pairs.foldl (fun m p=>m.insert p.1 p.2) m)[a]?=some d → P a d := by
  induction pairs generalizing m with
  | nil=>exact hm
  | cons p ps ih=>
    apply ih
    · intro a d hd
      rw [Std.HashMap.getElem?_insert] at hd
      split at hd
      · rename_i hkey
        have hk : p.1=a := by simpa using hkey
        have hv : p.2=d := Option.some.inj hd
        simpa only [hk,hv] using hp p List.mem_cons_self
      · exact hm a d hd
    · intro z hz;exact hp z (List.mem_cons_of_mem _ hz)

theorem forward_sound (size : Nat) (inverse : Nat → Nat) (a d : Nat)
    (hd : (forward size inverse)[a]?=some d) : 1≤d ∧ d<size ∧ inverse d=a := by
  apply fold_sound (fun a d=>1≤d ∧ d<size ∧ inverse d=a) (entries size inverse) ∅ ?_ ?_ a d hd
  · intro a d hh
    rw [Std.HashMap.getElem?_empty] at hh
    cases hh
  · intro p hp
    simp only [entries,List.mem_map] at hp
    obtain ⟨i,_,rfl⟩:=hp
    have hi:=i.isLt
    exact ⟨by omega,by omega,rfl⟩

theorem roundtrip (size : Nat) (inverse : Nat → Nat) (a : Nat) :
    decode size inverse (encode size (forward size inverse) a)=a := by
  unfold encode
  split
  · rename_i d hd
    have h:=forward_sound size inverse a d hd
    exact (if_pos h.2.1).trans h.2.2
  · simp [decode]

theorem encode_injective (size : Nat) (inverse : Nat → Nat) :
    Function.Injective (encode size (forward size inverse)) :=
  Function.LeftInverse.injective (roundtrip size inverse)

theorem encode_positive (size : Nat) (inverse : Nat → Nat) (hsize : 0<size) (a : Nat) :
    1≤encode size (forward size inverse) a := by
  unfold encode
  split
  · rename_i d hd;exact (forward_sound size inverse a d hd).1
  · omega

def literal (map : Nat → Nat) : Sat.Literal → Literal
  | .pos a=>(true,map a)
  | .neg a=>(false,map a)
def clause (map : Nat → Nat) (c : Sat.Clause) : List Literal := c.map (literal map)
def formula (map : Nat → Nat) (f : Sat.Fmla) : CNF := f.map (clause map)

noncomputable def valuation (v : Sat.Valuation) (back : Nat → Nat) : Valuation := by
  classical
  exact fun d=>decide (v (back d))

theorem clause_satisfied (v : Sat.Valuation) (map back : Nat → Nat)
    (hback : ∀a,back (map a)=a) (c : Sat.Clause) (hc : v.satisfies c) :
    ClauseSat (valuation v back) (clause map c) := by
  classical
  induction c with
  | nil=>exact False.elim hc
  | cons l ls ih=>
    cases l with
    | pos a=>
      by_cases ha : v a
      · refine ⟨(true,map a),by simp [clause,literal],?_⟩
        simpa only [valuation,hback,decide_eq_true_eq] using ha
      · have ht : v.satisfies ls:=hc ha
        obtain ⟨lit,hmem,hval⟩:=ih ht
        exact ⟨lit,List.mem_cons_of_mem _ hmem,hval⟩
    | neg a=>
      by_cases ha : v a
      · have ht : v.satisfies ls:=hc ha
        obtain ⟨lit,hmem,hval⟩:=ih ht
        exact ⟨lit,List.mem_cons_of_mem _ hmem,hval⟩
      · refine ⟨(false,map a),by simp [clause,literal],?_⟩
        simpa only [valuation,hback,decide_eq_false_iff_not] using ha

theorem formula_satisfied (v : Sat.Valuation) (map back : Nat → Nat)
    (hback : ∀a,back (map a)=a) (f : Sat.Fmla) (hf : v.satisfies_fmla f) :
    FormulaSat (valuation v back) (formula map f) := by
  intro c hc
  obtain ⟨source,hs,rfl⟩:=List.mem_map.mp hc
  exact clause_satisfied v map back hback source (hf.prop source hs)

theorem native_formula_satisfied (size : Nat) (inverse : Nat → Nat)
    (v : Sat.Valuation) (f : Sat.Fmla) (hf : v.satisfies_fmla f) :
    FormulaSat (valuation v (decode size inverse)) (formula (encode size (forward size inverse)) f) :=
  formula_satisfied v _ _ (roundtrip size inverse) f hf

#print axioms roundtrip
#print axioms native_formula_satisfied
end PricingIntegration.NativeRenaming
