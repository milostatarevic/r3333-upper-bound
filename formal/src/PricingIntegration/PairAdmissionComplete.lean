import PricingIntegration.PairAdmissionRow00
import PricingIntegration.PairAdmissionRow01
import PricingIntegration.PairAdmissionRow02
import PricingIntegration.PairAdmissionRow03
import PricingIntegration.PairAdmissionRow04
import PricingIntegration.PairAdmissionRow05
import PricingIntegration.PairAdmissionRow06
import PricingIntegration.PairAdmissionRow07
import PricingIntegration.PairAdmissionRow08
import PricingIntegration.PairAdmissionRow09
import PricingIntegration.PairAdmissionRow10
import PricingIntegration.PairAdmissionRow11
import PricingIntegration.PairAdmissionRow12
import PricingIntegration.PairAdmissionRow13
import PricingIntegration.PairAdmissionRow14
import PricingIntegration.PairAdmissionRow15
import PricingIntegration.PairAdmissionRow16
import PricingIntegration.PairAdmissionRow17
import PricingIntegration.PairAdmissionRow18
import PricingIntegration.PairAdmissionRow19
import PricingIntegration.PairAdmissionRow20
import PricingIntegration.PairAdmissionRow21
import PricingIntegration.PairAdmissionRow22
import PricingIntegration.PairAdmissionRow23
import PricingIntegration.PairAdmissionRow24
import PricingIntegration.PairAdmissionRow25
import PricingIntegration.PairAdmissionRow26
import PricingIntegration.PairAdmissionRow27
import PricingIntegration.PairAdmissionRow28
import PricingIntegration.PairAdmissionRow29
import PricingIntegration.PairAdmissionRow30
import PricingIntegration.PairAdmissionRow31
import PricingIntegration.PairAdmissionRow32
import PricingIntegration.PairAdmissionRow33
import PricingIntegration.PairAdmissionRow34
import PricingIntegration.PairAdmissionRow35
set_option autoImplicit false
namespace PricingIntegration.PairAdmission
open Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem all_rows_ok (i : Fin 36) : RowOK i := by
 fin_cases i
 · exact row00_ok
 · exact row01_ok
 · exact row02_ok
 · exact row03_ok
 · exact row04_ok
 · exact row05_ok
 · exact row06_ok
 · exact row07_ok
 · exact row08_ok
 · exact row09_ok
 · exact row10_ok
 · exact row11_ok
 · exact row12_ok
 · exact row13_ok
 · exact row14_ok
 · exact row15_ok
 · exact row16_ok
 · exact row17_ok
 · exact row18_ok
 · exact row19_ok
 · exact row20_ok
 · exact row21_ok
 · exact row22_ok
 · exact row23_ok
 · exact row24_ok
 · exact row25_ok
 · exact row26_ok
 · exact row27_ok
 · exact row28_ok
 · exact row29_ok
 · exact row30_ok
 · exact row31_ok
 · exact row32_ok
 · exact row33_ok
 · exact row34_ok
 · exact row35_ok

/-- Exhaustive products of the proved support representative lists reach
one of the exact737 native pairs. The only nonidentity admission is the
already available globalD/TT exchange of the two complete foreign cells. -/
theorem support_product_admitted (i : Fin 36) (a b : Finset Nat)
    (ha : a∈reps (row i).leftKind ((row i).stage==1))
    (hb : b∈reps (row i).rightKind ((row i).stage==2)) :
    ∃p : Fin 737,
      retained p=⟨(row i).family,(row i).leftKind,(row i).rightKind,(row i).stage,a,b⟩ ∨
      ((row i).family=2 ∧ (row i).leftKind=1 ∧ (row i).rightKind=1 ∧
       retained p=exchange ⟨(row i).family,(row i).leftKind,(row i).rightKind,(row i).stage,a,b⟩) := by
  have hp : (a,b)∈expected i := List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
  have hmem : (a,b)∈((original i).map fun e=>(e.left,e.right)).toFinset := by
    rw [(all_rows_ok i).1];exact List.mem_toFinset.mpr hp
  obtain ⟨e,he,heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hmem)
  have h := (all_rows_ok i).2 e he
  have hleft : e.left=a := congrArg Prod.fst heq
  have hright : e.right=b := congrArg Prod.snd heq
  refine ⟨⟨e.target,h.1⟩,?_⟩
  by_cases hs : e.swapped=true
  · have ht := h.2
    simp [hs] at ht
    exact Or.inr ⟨ht.1,ht.2.1,ht.2.2.1,by simpa only [retained,source,hleft,hright] using ht.2.2.2⟩
  · have ht := h.2
    simp [hs] at ht
    exact Or.inl (by simpa only [retained,source,hleft,hright] using ht)

#print axioms support_product_admitted
end PricingIntegration.PairAdmission
