import PricingC.Rooted45Lookup0_0
import PricingC.Rooted45Lookup0_1
import PricingC.Rooted45Lookup0_2
import PricingC.Rooted45Lookup0_3
import PricingC.Rooted45Lookup0_4
import PricingC.Rooted45Lookup0_5
import PricingC.Rooted45Lookup0_6
import PricingC.Rooted45Lookup0_7
import PricingC.Rooted45Lookup0_8
import PricingC.Rooted45Lookup0_9
import PricingC.Rooted45Lookup0_10
import PricingC.Rooted45Lookup0_11
import PricingC.Rooted45Lookup1_0
import PricingC.Rooted45Lookup1_1
import PricingC.Rooted45Lookup1_2
import PricingC.Rooted45Lookup1_3
import PricingC.Rooted45Lookup1_4
import PricingC.Rooted45Lookup1_5
import PricingC.Rooted45Lookup1_6
import PricingC.Rooted45Lookup1_7
import PricingC.Rooted45Lookup1_8
import PricingC.Rooted45Lookup1_9
import PricingC.Rooted45Lookup1_10
import PricingC.Rooted45Lookup1_11
namespace PricingC.Rooted45Orientation

def blockIndex (q : Fin 12) (j : Fin 50) : Fin 600 := ⟨50*q.val+j.val,by omega⟩

theorem all_indexed_transport (k : Bool) (q : Fin 12) : ∀ j : Fin 50,∀ a b : Fin 14,a≠b →
 matrix k (word (candidate k (target k (blockIndex q j)))) a b =
 colorBack k (PricingABD.P15MatrixTransport.matrix
 (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate (blockIndex q j)))
 (oldIndex k a) (oldIndex k b)) := by
 cases k <;> fin_cases q
 · exact rooted45_lookup0_0
 · exact rooted45_lookup0_1
 · exact rooted45_lookup0_2
 · exact rooted45_lookup0_3
 · exact rooted45_lookup0_4
 · exact rooted45_lookup0_5
 · exact rooted45_lookup0_6
 · exact rooted45_lookup0_7
 · exact rooted45_lookup0_8
 · exact rooted45_lookup0_9
 · exact rooted45_lookup0_10
 · exact rooted45_lookup0_11
 · exact rooted45_lookup1_0
 · exact rooted45_lookup1_1
 · exact rooted45_lookup1_2
 · exact rooted45_lookup1_3
 · exact rooted45_lookup1_4
 · exact rooted45_lookup1_5
 · exact rooted45_lookup1_6
 · exact rooted45_lookup1_7
 · exact rooted45_lookup1_8
 · exact rooted45_lookup1_9
 · exact rooted45_lookup1_10
 · exact rooted45_lookup1_11

theorem full_matrix_transport (k : Bool) (i : Fin 600) (a b : Fin 14) (hab:a≠b) :
 matrix k (word (candidate k (target k i))) a b =
 colorBack k (PricingABD.P15MatrixTransport.matrix
 (PricingABD.P15MatrixTransport.word (PricingABD.P15PairOrbit.candidate i))
 (oldIndex k a) (oldIndex k b)) := by
 let q:Fin 12:=⟨i.val/50,by omega⟩
 let j:Fin 50:=⟨i.val%50,Nat.mod_lt _ (by decide)⟩
 have hi:blockIndex q j=i:=by apply Fin.ext;dsimp[blockIndex,q,j];omega
 rw [←hi]
 exact all_indexed_transport k q j a b hab
#print axioms full_matrix_transport
end PricingC.Rooted45Orientation
