import PricingC.NativeChoiceChunk0
import PricingC.NativeChoiceChunk1
import PricingC.NativeChoiceChunk2
import PricingC.NativeChoiceChunk3
namespace PricingC.NativePairActions
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem selected_choice_correct : ∀t:Fin 56,∀i:Fin 600,
 selectedIndex t i<choiceCount t ∧ choice t (selectedIndex t i)=selectedCode t i:=by
 intro t
 fin_cases t
 · exact selected_choice_00
 · exact selected_choice_01
 · exact selected_choice_02
 · exact selected_choice_03
 · exact selected_choice_04
 · exact selected_choice_05
 · exact selected_choice_06
 · exact selected_choice_07
 · exact selected_choice_08
 · exact selected_choice_09
 · exact selected_choice_10
 · exact selected_choice_11
 · exact selected_choice_12
 · exact selected_choice_13
 · exact selected_choice_14
 · exact selected_choice_15
 · exact selected_choice_16
 · exact selected_choice_17
 · exact selected_choice_18
 · exact selected_choice_19
 · exact selected_choice_20
 · exact selected_choice_21
 · exact selected_choice_22
 · exact selected_choice_23
 · exact selected_choice_24
 · exact selected_choice_25
 · exact selected_choice_26
 · exact selected_choice_27
 · exact selected_choice_28
 · exact selected_choice_29
 · exact selected_choice_30
 · exact selected_choice_31
 · exact selected_choice_32
 · exact selected_choice_33
 · exact selected_choice_34
 · exact selected_choice_35
 · exact selected_choice_36
 · exact selected_choice_37
 · exact selected_choice_38
 · exact selected_choice_39
 · exact selected_choice_40
 · exact selected_choice_41
 · exact selected_choice_42
 · exact selected_choice_43
 · exact selected_choice_44
 · exact selected_choice_45
 · exact selected_choice_46
 · exact selected_choice_47
 · exact selected_choice_48
 · exact selected_choice_49
 · exact selected_choice_50
 · exact selected_choice_51
 · exact selected_choice_52
 · exact selected_choice_53
 · exact selected_choice_54
 · exact selected_choice_55
#print axioms selected_choice_correct
end PricingC.NativePairActions
