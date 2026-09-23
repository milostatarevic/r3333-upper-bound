import PricingC.AllNativeTableAudit
set_option autoImplicit false
namespace CompletionC.NativeMatrices

inductive Shape where
 | freeFour | leftFour | rightFour | allFive
 deriving DecidableEq, Fintype
namespace Shape
def code : Shape → Nat
 | .freeFour=>0 | .leftFour=>1 | .rightFour=>2 | .allFive=>3
def free : Shape → Nat
 | .freeFour=>4 | _=>5
def left : Shape → Nat
 | .leftFour=>4 | _=>5
def right : Shape → Nat
 | .rightFour=>4 | _=>5
def dimension : Shape → Nat
 | .allFive=>15 | _=>14
theorem dimension_sum (s:Shape):s.dimension=s.free+s.left+s.right:=by cases s <;> rfl
theorem dimension_positive (s:Shape):0<s.dimension:=by cases s <;> decide
end Shape

def candidate : Shape→Fin 600→Nat
 | .freeFour,i=>PricingABD.P15PairOrbit.candidate i
 | .leftFour,i=>PricingC.Rooted45Orientation.candidate false i
 | .rightFour,i=>PricingC.Rooted45Orientation.candidate true i
 | .allFive,i=>PricingC.Rooted555.candidate i

def matrix : (s:Shape)→Nat→Fin s.dimension→Fin s.dimension→Fin 4
 | .freeFour,w,a,b=>PricingABD.P15MatrixTransport.matrix (PricingABD.P15MatrixTransport.word w) a b
 | .leftFour,w,a,b=>PricingC.Rooted45Orientation.matrix false (PricingC.Rooted45Orientation.word w) a b
 | .rightFour,w,a,b=>PricingC.Rooted45Orientation.matrix true (PricingC.Rooted45Orientation.word w) a b
 | .allFive,w,a,b=>PricingC.Rooted555.matrix (PricingC.Rooted555.word w) a b

/-- The accepted native table functions are reused directly; no new copies of
candidate words, representative words, or matrix identities occur here. -/
structure Table where
 shape:Shape
 count:Nat
 representative:Fin count→Nat
 target:Fin 600→Fin count
 coordinate:Fin 600→Fin shape.dimension→Fin shape.dimension

def table (t:Fin 56):Table:=match t.val with
 | 0=>⟨.rightFour,16,PricingC.RemainingOrbit00.representative,PricingC.RemainingOrbit00.target,PricingC.RemainingOrbit00.coordinate⟩
 | 1=>⟨.allFive,30,PricingC.RemainingOrbit01.representative,PricingC.RemainingOrbit01.target,PricingC.RemainingOrbit01.coordinate⟩
 | 2=>⟨.allFive,30,PricingC.RemainingOrbit02.representative,PricingC.RemainingOrbit02.target,PricingC.RemainingOrbit02.coordinate⟩
 | 3=>⟨.leftFour,30,PricingC.RemainingOrbit03.representative,PricingC.RemainingOrbit03.target,PricingC.RemainingOrbit03.coordinate⟩
 | 4=>⟨.freeFour,16,PricingC.RemainingOrbit04.representative,PricingC.RemainingOrbit04.target,PricingC.RemainingOrbit04.coordinate⟩
 | 5=>⟨.rightFour,30,PricingC.RemainingOrbit05.representative,PricingC.RemainingOrbit05.target,PricingC.RemainingOrbit05.coordinate⟩
 | 6=>⟨.freeFour,150,PricingC.RemainingOrbit06.representative,PricingC.RemainingOrbit06.target,PricingC.RemainingOrbit06.coordinate⟩
 | 7=>⟨.allFive,16,PricingC.RemainingOrbit07.representative,PricingC.RemainingOrbit07.target,PricingC.RemainingOrbit07.coordinate⟩
 | 8=>⟨.freeFour,30,PricingC.RemainingOrbit08.representative,PricingC.RemainingOrbit08.target,PricingC.RemainingOrbit08.coordinate⟩
 | 9=>⟨.leftFour,6,PricingC.RemainingOrbit09.representative,PricingC.RemainingOrbit09.target,PricingC.RemainingOrbit09.coordinate⟩
 | 10=>⟨.allFive,4,PricingC.RemainingOrbit10.representative,PricingC.RemainingOrbit10.target,PricingC.RemainingOrbit10.coordinate⟩
 | 11=>⟨.leftFour,60,PricingC.RemainingOrbit11.representative,PricingC.RemainingOrbit11.target,PricingC.RemainingOrbit11.coordinate⟩
 | 12=>⟨.allFive,4,PricingC.RemainingOrbit12.representative,PricingC.RemainingOrbit12.target,PricingC.RemainingOrbit12.coordinate⟩
 | 13=>⟨.freeFour,16,PricingC.RemainingOrbit13.representative,PricingC.RemainingOrbit13.target,PricingC.RemainingOrbit13.coordinate⟩
 | 14=>⟨.freeFour,150,PricingC.RemainingOrbit14.representative,PricingC.RemainingOrbit14.target,PricingC.RemainingOrbit14.coordinate⟩
 | 15=>⟨.leftFour,16,PricingC.RemainingOrbit15.representative,PricingC.RemainingOrbit15.target,PricingC.RemainingOrbit15.coordinate⟩
 | 16=>⟨.rightFour,6,PricingC.RemainingOrbit16.representative,PricingC.RemainingOrbit16.target,PricingC.RemainingOrbit16.coordinate⟩
 | 17=>⟨.allFive,16,PricingC.RemainingOrbit17.representative,PricingC.RemainingOrbit17.target,PricingC.RemainingOrbit17.coordinate⟩
 | 18=>⟨.rightFour,30,PricingC.RemainingOrbit18.representative,PricingC.RemainingOrbit18.target,PricingC.RemainingOrbit18.coordinate⟩
 | 19=>⟨.rightFour,60,PricingC.RemainingOrbit19.representative,PricingC.RemainingOrbit19.target,PricingC.RemainingOrbit19.coordinate⟩
 | 20=>⟨.freeFour,76,PricingC.RemainingOrbit20.representative,PricingC.RemainingOrbit20.target,PricingC.RemainingOrbit20.coordinate⟩
 | 21=>⟨.allFive,2,PricingC.RemainingOrbit21.representative,PricingC.RemainingOrbit21.target,PricingC.RemainingOrbit21.coordinate⟩
 | 22=>⟨.allFive,30,PricingC.RemainingOrbit22.representative,PricingC.RemainingOrbit22.target,PricingC.RemainingOrbit22.coordinate⟩
 | 23=>⟨.freeFour,76,PricingC.RemainingOrbit23.representative,PricingC.RemainingOrbit23.target,PricingC.RemainingOrbit23.coordinate⟩
 | 24=>⟨.freeFour,150,PricingC.RemainingOrbit24.representative,PricingC.RemainingOrbit24.target,PricingC.RemainingOrbit24.coordinate⟩
 | 25=>⟨.freeFour,76,PricingC.RemainingOrbit25.representative,PricingC.RemainingOrbit25.target,PricingC.RemainingOrbit25.coordinate⟩
 | 26=>⟨.allFive,6,PricingC.RemainingOrbit26.representative,PricingC.RemainingOrbit26.target,PricingC.RemainingOrbit26.coordinate⟩
 | 27=>⟨.rightFour,16,PricingC.RemainingOrbit27.representative,PricingC.RemainingOrbit27.target,PricingC.RemainingOrbit27.coordinate⟩
 | 28=>⟨.freeFour,150,PricingC.RemainingOrbit28.representative,PricingC.RemainingOrbit28.target,PricingC.RemainingOrbit28.coordinate⟩
 | 29=>⟨.leftFour,30,PricingC.RemainingOrbit29.representative,PricingC.RemainingOrbit29.target,PricingC.RemainingOrbit29.coordinate⟩
 | 30=>⟨.freeFour,16,PricingC.RemainingOrbit30.representative,PricingC.RemainingOrbit30.target,PricingC.RemainingOrbit30.coordinate⟩
 | 31=>⟨.allFive,60,PricingC.RemainingOrbit31.representative,PricingC.RemainingOrbit31.target,PricingC.RemainingOrbit31.coordinate⟩
 | 32=>⟨.freeFour,300,PricingC.RemainingOrbit32.representative,PricingC.RemainingOrbit32.target,PricingC.RemainingOrbit32.coordinate⟩
 | 33=>⟨.rightFour,30,PricingC.RemainingOrbit33.representative,PricingC.RemainingOrbit33.target,PricingC.RemainingOrbit33.coordinate⟩
 | 34=>⟨.rightFour,30,PricingC.RemainingOrbit34.representative,PricingC.RemainingOrbit34.target,PricingC.RemainingOrbit34.coordinate⟩
 | 35=>⟨.freeFour,16,PricingC.RemainingOrbit35.representative,PricingC.RemainingOrbit35.target,PricingC.RemainingOrbit35.coordinate⟩
 | 36=>⟨.allFive,16,PricingC.RemainingOrbit36.representative,PricingC.RemainingOrbit36.target,PricingC.RemainingOrbit36.coordinate⟩
 | 37=>⟨.leftFour,4,PricingC.RemainingOrbit37.representative,PricingC.RemainingOrbit37.target,PricingC.RemainingOrbit37.coordinate⟩
 | 38=>⟨.allFive,4,PricingC.RemainingOrbit38.representative,PricingC.RemainingOrbit38.target,PricingC.RemainingOrbit38.coordinate⟩
 | 39=>⟨.rightFour,4,PricingC.RemainingOrbit39.representative,PricingC.RemainingOrbit39.target,PricingC.RemainingOrbit39.coordinate⟩
 | 40=>⟨.allFive,30,PricingC.RemainingOrbit40.representative,PricingC.RemainingOrbit40.target,PricingC.RemainingOrbit40.coordinate⟩
 | 41=>⟨.allFive,30,PricingC.RemainingOrbit41.representative,PricingC.RemainingOrbit41.target,PricingC.RemainingOrbit41.coordinate⟩
 | 42=>⟨.allFive,16,PricingC.RemainingOrbit42.representative,PricingC.RemainingOrbit42.target,PricingC.RemainingOrbit42.coordinate⟩
 | 43=>⟨.freeFour,150,PricingC.RemainingOrbit43.representative,PricingC.RemainingOrbit43.target,PricingC.RemainingOrbit43.coordinate⟩
 | 44=>⟨.rightFour,16,PricingC.RemainingOrbit44.representative,PricingC.RemainingOrbit44.target,PricingC.RemainingOrbit44.coordinate⟩
 | 45=>⟨.freeFour,76,PricingC.RemainingOrbit45.representative,PricingC.RemainingOrbit45.target,PricingC.RemainingOrbit45.coordinate⟩
 | 46=>⟨.freeFour,16,PricingC.RemainingOrbit46.representative,PricingC.RemainingOrbit46.target,PricingC.RemainingOrbit46.coordinate⟩
 | 47=>⟨.allFive,4,PricingC.RemainingOrbit47.representative,PricingC.RemainingOrbit47.target,PricingC.RemainingOrbit47.coordinate⟩
 | 48=>⟨.allFive,6,PricingC.RemainingOrbit48.representative,PricingC.RemainingOrbit48.target,PricingC.RemainingOrbit48.coordinate⟩
 | 49=>⟨.freeFour,30,PricingC.RemainingOrbit49.representative,PricingC.RemainingOrbit49.target,PricingC.RemainingOrbit49.coordinate⟩
 | 50=>⟨.leftFour,30,PricingC.RemainingOrbit50.representative,PricingC.RemainingOrbit50.target,PricingC.RemainingOrbit50.coordinate⟩
 | 51=>⟨.leftFour,16,PricingC.RemainingOrbit51.representative,PricingC.RemainingOrbit51.target,PricingC.RemainingOrbit51.coordinate⟩
 | 52=>⟨.freeFour,76,PricingC.RemainingOrbit52.representative,PricingC.RemainingOrbit52.target,PricingC.RemainingOrbit52.coordinate⟩
 | 53=>⟨.allFive,16,PricingC.RemainingOrbit53.representative,PricingC.RemainingOrbit53.target,PricingC.RemainingOrbit53.coordinate⟩
 | 54=>⟨.freeFour,4,PricingC.RemainingOrbit54.representative,PricingC.RemainingOrbit54.target,PricingC.RemainingOrbit54.coordinate⟩
 | 55=>⟨.allFive,4,PricingC.RemainingOrbit55.representative,PricingC.RemainingOrbit55.target,PricingC.RemainingOrbit55.coordinate⟩
 | _=>⟨.freeFour,150,PricingC.RemainingOrbit06.representative,PricingC.RemainingOrbit06.target,PricingC.RemainingOrbit06.coordinate⟩

/-- Every selected action transports the complete matrix, including the
internal free and foreign support edges. This joins existing proved tables. -/
theorem complete_cover (t:Fin 56):∀i:Fin 600,∀a b:Fin (table t).shape.dimension,a≠b→
 matrix (table t).shape ((table t).representative ((table t).target i)) a b=
 matrix (table t).shape (candidate (table t).shape i) ((table t).coordinate i a) ((table t).coordinate i b):=by
 fin_cases t
 · exact PricingC.RemainingOrbit00.complete_matrix_cover
 · exact PricingC.RemainingOrbit01.complete_matrix_cover
 · exact PricingC.RemainingOrbit02.complete_matrix_cover
 · exact PricingC.RemainingOrbit03.complete_matrix_cover
 · exact PricingC.RemainingOrbit04.complete_matrix_cover
 · exact PricingC.RemainingOrbit05.complete_matrix_cover
 · exact PricingC.RemainingOrbit06.complete_matrix_cover
 · exact PricingC.RemainingOrbit07.complete_matrix_cover
 · exact PricingC.RemainingOrbit08.complete_matrix_cover
 · exact PricingC.RemainingOrbit09.complete_matrix_cover
 · exact PricingC.RemainingOrbit10.complete_matrix_cover
 · exact PricingC.RemainingOrbit11.complete_matrix_cover
 · exact PricingC.RemainingOrbit12.complete_matrix_cover
 · exact PricingC.RemainingOrbit13.complete_matrix_cover
 · exact PricingC.RemainingOrbit14.complete_matrix_cover
 · exact PricingC.RemainingOrbit15.complete_matrix_cover
 · exact PricingC.RemainingOrbit16.complete_matrix_cover
 · exact PricingC.RemainingOrbit17.complete_matrix_cover
 · exact PricingC.RemainingOrbit18.complete_matrix_cover
 · exact PricingC.RemainingOrbit19.complete_matrix_cover
 · exact PricingC.RemainingOrbit20.complete_matrix_cover
 · exact PricingC.RemainingOrbit21.complete_matrix_cover
 · exact PricingC.RemainingOrbit22.complete_matrix_cover
 · exact PricingC.RemainingOrbit23.complete_matrix_cover
 · exact PricingC.RemainingOrbit24.complete_matrix_cover
 · exact PricingC.RemainingOrbit25.complete_matrix_cover
 · exact PricingC.RemainingOrbit26.complete_matrix_cover
 · exact PricingC.RemainingOrbit27.complete_matrix_cover
 · exact PricingC.RemainingOrbit28.complete_matrix_cover
 · exact PricingC.RemainingOrbit29.complete_matrix_cover
 · exact PricingC.RemainingOrbit30.complete_matrix_cover
 · exact PricingC.RemainingOrbit31.complete_matrix_cover
 · exact PricingC.RemainingOrbit32.complete_matrix_cover
 · exact PricingC.RemainingOrbit33.complete_matrix_cover
 · exact PricingC.RemainingOrbit34.complete_matrix_cover
 · exact PricingC.RemainingOrbit35.complete_matrix_cover
 · exact PricingC.RemainingOrbit36.complete_matrix_cover
 · exact PricingC.RemainingOrbit37.complete_matrix_cover
 · exact PricingC.RemainingOrbit38.complete_matrix_cover
 · exact PricingC.RemainingOrbit39.complete_matrix_cover
 · exact PricingC.RemainingOrbit40.complete_matrix_cover
 · exact PricingC.RemainingOrbit41.complete_matrix_cover
 · exact PricingC.RemainingOrbit42.complete_matrix_cover
 · exact PricingC.RemainingOrbit43.complete_matrix_cover
 · exact PricingC.RemainingOrbit44.complete_matrix_cover
 · exact PricingC.RemainingOrbit45.complete_matrix_cover
 · exact PricingC.RemainingOrbit46.complete_matrix_cover
 · exact PricingC.RemainingOrbit47.complete_matrix_cover
 · exact PricingC.RemainingOrbit48.complete_matrix_cover
 · exact PricingC.RemainingOrbit49.complete_matrix_cover
 · exact PricingC.RemainingOrbit50.complete_matrix_cover
 · exact PricingC.RemainingOrbit51.complete_matrix_cover
 · exact PricingC.RemainingOrbit52.complete_matrix_cover
 · exact PricingC.RemainingOrbit53.complete_matrix_cover
 · exact PricingC.RemainingOrbit54.complete_matrix_cover
 · exact PricingC.RemainingOrbit55.complete_matrix_cover

theorem coordinate_selected (t:Fin 56):∀i:Fin 600,∀a:Fin (table t).shape.dimension,
 ((table t).coordinate i a).val=
 PricingC.NativeBlockActions.digit (PricingC.NativePairActions.selectedCode t i) a.val % (table t).shape.dimension:=by
 fin_cases t
 · exact PricingC.NativePairActions.selected_coordinate_00
 · exact PricingC.NativePairActions.selected_coordinate_01
 · exact PricingC.NativePairActions.selected_coordinate_02
 · exact PricingC.NativePairActions.selected_coordinate_03
 · exact PricingC.NativePairActions.selected_coordinate_04
 · exact PricingC.NativePairActions.selected_coordinate_05
 · exact PricingC.NativePairActions.selected_coordinate_06
 · exact PricingC.NativePairActions.selected_coordinate_07
 · exact PricingC.NativePairActions.selected_coordinate_08
 · exact PricingC.NativePairActions.selected_coordinate_09
 · exact PricingC.NativePairActions.selected_coordinate_10
 · exact PricingC.NativePairActions.selected_coordinate_11
 · exact PricingC.NativePairActions.selected_coordinate_12
 · exact PricingC.NativePairActions.selected_coordinate_13
 · exact PricingC.NativePairActions.selected_coordinate_14
 · exact PricingC.NativePairActions.selected_coordinate_15
 · exact PricingC.NativePairActions.selected_coordinate_16
 · exact PricingC.NativePairActions.selected_coordinate_17
 · exact PricingC.NativePairActions.selected_coordinate_18
 · exact PricingC.NativePairActions.selected_coordinate_19
 · exact PricingC.NativePairActions.selected_coordinate_20
 · exact PricingC.NativePairActions.selected_coordinate_21
 · exact PricingC.NativePairActions.selected_coordinate_22
 · exact PricingC.NativePairActions.selected_coordinate_23
 · exact PricingC.NativePairActions.selected_coordinate_24
 · exact PricingC.NativePairActions.selected_coordinate_25
 · exact PricingC.NativePairActions.selected_coordinate_26
 · exact PricingC.NativePairActions.selected_coordinate_27
 · exact PricingC.NativePairActions.selected_coordinate_28
 · exact PricingC.NativePairActions.selected_coordinate_29
 · exact PricingC.NativePairActions.selected_coordinate_30
 · exact PricingC.NativePairActions.selected_coordinate_31
 · exact PricingC.NativePairActions.selected_coordinate_32
 · exact PricingC.NativePairActions.selected_coordinate_33
 · exact PricingC.NativePairActions.selected_coordinate_34
 · exact PricingC.NativePairActions.selected_coordinate_35
 · exact PricingC.NativePairActions.selected_coordinate_36
 · exact PricingC.NativePairActions.selected_coordinate_37
 · exact PricingC.NativePairActions.selected_coordinate_38
 · exact PricingC.NativePairActions.selected_coordinate_39
 · exact PricingC.NativePairActions.selected_coordinate_40
 · exact PricingC.NativePairActions.selected_coordinate_41
 · exact PricingC.NativePairActions.selected_coordinate_42
 · exact PricingC.NativePairActions.selected_coordinate_43
 · exact PricingC.NativePairActions.selected_coordinate_44
 · exact PricingC.NativePairActions.selected_coordinate_45
 · exact PricingC.NativePairActions.selected_coordinate_46
 · exact PricingC.NativePairActions.selected_coordinate_47
 · exact PricingC.NativePairActions.selected_coordinate_48
 · exact PricingC.NativePairActions.selected_coordinate_49
 · exact PricingC.NativePairActions.selected_coordinate_50
 · exact PricingC.NativePairActions.selected_coordinate_51
 · exact PricingC.NativePairActions.selected_coordinate_52
 · exact PricingC.NativePairActions.selected_coordinate_53
 · exact PricingC.NativePairActions.selected_coordinate_54
 · exact PricingC.NativePairActions.selected_coordinate_55

theorem representative_count_positive (t:Fin 56):0<(table t).count:=by
 fin_cases t <;> decide
#print axioms complete_cover
#print axioms coordinate_selected
end CompletionC.NativeMatrices
