import UniformK61.UUCheckRow00
import UniformK61.UUCheckRow01
import UniformK61.UUCheckRow02
import UniformK61.UUCheckRow03
import UniformK61.UUCheckRow04
import UniformK61.UUCheckRow05
import UniformK61.UUCheckRow06
import UniformK61.UUCheckRow07
import UniformK61.UUCheckRow08
import UniformK61.UUCheckRow09
import UniformK61.UUCheckRow10
import UniformK61.UUCheckRow11
import UniformK61.UUCheckRow12
import UniformK61.UUCheckRow13
import UniformK61.UUCheckRow14
import UniformK61.UUCheckRow15
import UniformK61.UUCheckRow16
import UniformK61.UUCheckRow17
import UniformK61.UUCheckRow18
import UniformK61.UUCheckRow19
import UniformK61.UUCheckRow20
import UniformK61.UUCheckRow21
import UniformK61.UUCheckRow22
import UniformK61.UUCheckRow23
import UniformK61.UUCheckRow24
import UniformK61.UUCheckRow25
import UniformK61.UUCheckRow26
import UniformK61.UUCheckRow27
import UniformK61.UUCheckRow28
import UniformK61.UUCheckRow29
import UniformK61.UUCheckRow30
import UniformK61.UUCheckRow31
import UniformK61.UUCheckRow32
import UniformK61.UUCheckRow33
import UniformK61.UUCheckRow34
import UniformK61.UUCheckRow35
import UniformK61.UUCheckRow36
import UniformK61.UUCheckRow37
import UniformK61.UUCheckRow38
import UniformK61.UUCheckRow39
import UniformK61.UUCheckRow40
import UniformK61.UUCheckRow41
import UniformK61.UUCheckRow42
import UniformK61.UUCheckRow43
import UniformK61.UUCheckRow44
import UniformK61.UUCheckRow45
import UniformK61.UUCheckRow46
import UniformK61.UUCheckRow47
import UniformK61.UUCheckRow48
import UniformK61.UUCheckRow49
import UniformK61.UUCheckRow50
import UniformK61.UUCheckRow51
import UniformK61.UUCheckRow52
import UniformK61.UUCheckRow53
import UniformK61.UUCheckRow54
import UniformK61.UUCheckRow55
import UniformK61.UUCheckRow56
import UniformK61.UUCheckRow57
import UniformK61.UUCheckRow58
import UniformK61.UUCheckRow59
import UniformK61.UUCheckRow60
import UniformK61.UUCheckRow61
import UniformK61.UUCheckRow62
import UniformK61.UUCheckRow63
import UniformK61.UUCheckRow64
import UniformK61.UUCheckRow65
import UniformK61.UUResidualTransport
set_option autoImplicit false
namespace UniformK61.UUChecks
open UniformK61.UUBridgeData UniformK61.UUSupportData

theorem residual_all_false (p : Pair) (i : Fin 600) : checkResidual false p i=true := by
 fin_cases p
 · exact UUCheckRow00.checked i
 · exact UUCheckRow01.checked i
 · exact UUCheckRow02.checked i
 · exact UUCheckRow03.checked i
 · exact UUCheckRow04.checked i
 · exact UUCheckRow05.checked i
 · exact UUCheckRow06.checked i
 · exact UUCheckRow07.checked i
 · exact UUCheckRow08.checked i
 · exact UUCheckRow09.checked i
 · exact UUCheckRow10.checked i
 · exact UUCheckRow11.checked i
 · exact UUCheckRow12.checked i
 · exact UUCheckRow13.checked i
 · exact UUCheckRow14.checked i
 · exact UUCheckRow15.checked i
 · exact UUCheckRow16.checked i
 · exact UUCheckRow17.checked i
 · exact UUCheckRow18.checked i
 · exact UUCheckRow19.checked i
 · exact UUCheckRow20.checked i
 · exact UUCheckRow21.checked i
 · exact UUCheckRow22.checked i
 · exact UUCheckRow23.checked i
 · exact UUCheckRow24.checked i
 · exact UUCheckRow25.checked i
 · exact UUCheckRow26.checked i
 · exact UUCheckRow27.checked i
 · exact UUCheckRow28.checked i
 · exact UUCheckRow29.checked i
 · exact UUCheckRow30.checked i
 · exact UUCheckRow31.checked i
 · exact UUCheckRow32.checked i
 · exact UUCheckRow33.checked i
 · exact UUCheckRow34.checked i
 · exact UUCheckRow35.checked i
 · exact UUCheckRow36.checked i
 · exact UUCheckRow37.checked i
 · exact UUCheckRow38.checked i
 · exact UUCheckRow39.checked i
 · exact UUCheckRow40.checked i
 · exact UUCheckRow41.checked i
 · exact UUCheckRow42.checked i
 · exact UUCheckRow43.checked i
 · exact UUCheckRow44.checked i
 · exact UUCheckRow45.checked i
 · exact UUCheckRow46.checked i
 · exact UUCheckRow47.checked i
 · exact UUCheckRow48.checked i
 · exact UUCheckRow49.checked i
 · exact UUCheckRow50.checked i
 · exact UUCheckRow51.checked i
 · exact UUCheckRow52.checked i
 · exact UUCheckRow53.checked i
 · exact UUCheckRow54.checked i
 · exact UUCheckRow55.checked i
 · exact UUCheckRow56.checked i
 · exact UUCheckRow57.checked i
 · exact UUCheckRow58.checked i
 · exact UUCheckRow59.checked i
 · exact UUCheckRow60.checked i
 · exact UUCheckRow61.checked i
 · exact UUCheckRow62.checked i
 · exact UUCheckRow63.checked i
 · exact UUCheckRow64.checked i
 · exact UUCheckRow65.checked i

theorem residual_all (q : Bool) (p : Pair) (i : Fin 600) : checkResidual q p i=true := by
 cases q
 · exact residual_all_false p i
 · rw[UUResidualTransport.checkResidual_q]
   exact residual_all_false p i

#print axioms residual_all
end UniformK61.UUChecks
