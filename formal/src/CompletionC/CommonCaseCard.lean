import CompletionC.CommonCaseCountDefs
set_option autoImplicit false
namespace CompletionC.CommonCaseCount
open PricingABD.ABLayout CompletionC.NativeFamilyJoin CompletionC.NativeMatrices
open PricingIntegration.NativeCommonCases Finset

theorem card_sum:Fintype.card Case=
 ∑l:Layout,∑t:Types,∑p:Fin 737,if Admitted l t p then (pairTable p).count else 0:=by
 simp only[Case,Fintype.card_sigma,Fintype.card_fin]
 apply Finset.sum_congr rfl
 intro l _
 apply Finset.sum_congr rfl
 intro t _
 rw[←Finset.sum_filter]
 exact (Finset.sum_subtype (univ.filter (Admitted l t)) (by simp) (fun p=>(pairTable p).count)).symm

theorem rowCount_sum (l:Layout) (t:Types):rowCount l t=∑p:Fin 737,if Admitted l t p then (pairTable p).count else 0:=by
 unfold rowCount
 rw[←List.sum_toFinset _ (List.nodup_finRange 737),List.toFinset_finRange]

theorem layouts_nodup:layouts.Nodup:=by decide +kernel
theorem layouts_complete:layouts.toFinset=(univ:Finset Layout):=by decide +kernel
theorem types_nodup:types.Nodup:=by decide +kernel
theorem types_complete:types.toFinset=(univ:Finset Types):=by decide +kernel

theorem cardinality_eq_executable:Fintype.card Case=executableCount:=by
 rw[card_sum]
 unfold executableCount
 rw[←List.sum_toFinset _ layouts_nodup,layouts_complete]
 apply Finset.sum_congr rfl
 intro l _
 rw[←List.sum_toFinset _ types_nodup,types_complete]
 apply Finset.sum_congr rfl
 intro t _
 exact (rowCount_sum l t).symm
#print axioms cardinality_eq_executable
end CompletionC.CommonCaseCount
