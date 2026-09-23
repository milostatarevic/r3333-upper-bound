import PricingC.GCaseClosures000
import PricingC.GCaseClosures001
import PricingC.GCaseClosures002
import PricingC.GCaseClosures003
import PricingC.GCaseClosures004
import PricingC.GCaseClosures005
import PricingC.GCaseClosures006
import PricingC.GCaseClosures007
import PricingC.GCaseClosures008
import PricingC.GCaseClosures009
import PricingC.GCaseClosures010
import PricingC.GCaseClosures011
import PricingC.GCaseClosures012
import PricingC.GCaseClosures013
import PricingC.GCaseClosures014
import PricingC.GCaseClosures015
import PricingC.GCaseClosures016
import PricingC.GCaseClosures017
import PricingC.GCaseClosures018
import PricingC.GCaseClosures019
import PricingC.GCaseClosures020
import PricingC.GCaseClosures021
import PricingC.GCaseClosures022
import PricingC.GCaseClosures023
import PricingC.GCaseClosures024
import PricingC.GCaseClosures025
import PricingC.GCaseClosures026
import PricingC.GCaseClosures027
import PricingC.GCaseClosures028
import PricingC.GCaseClosures029
import PricingC.GCaseClosures030
import PricingC.GCaseClosures031
import PricingC.GCaseClosures032
import PricingC.GCaseClosures033
import PricingC.GCaseClosures034
import PricingC.GCaseClosures035

namespace PricingC.GIsomorphic

theorem blocks_closed (b : Fin 36) (i : Fin 100) : CoreExcluded (caseCore (blockCase b i)) := by
 fin_cases b
 · exact block_closed000 i
 · exact block_closed001 i
 · exact block_closed002 i
 · exact block_closed003 i
 · exact block_closed004 i
 · exact block_closed005 i
 · exact block_closed006 i
 · exact block_closed007 i
 · exact block_closed008 i
 · exact block_closed009 i
 · exact block_closed010 i
 · exact block_closed011 i
 · exact block_closed012 i
 · exact block_closed013 i
 · exact block_closed014 i
 · exact block_closed015 i
 · exact block_closed016 i
 · exact block_closed017 i
 · exact block_closed018 i
 · exact block_closed019 i
 · exact block_closed020 i
 · exact block_closed021 i
 · exact block_closed022 i
 · exact block_closed023 i
 · exact block_closed024 i
 · exact block_closed025 i
 · exact block_closed026 i
 · exact block_closed027 i
 · exact block_closed028 i
 · exact block_closed029 i
 · exact block_closed030 i
 · exact block_closed031 i
 · exact block_closed032 i
 · exact block_closed033 i
 · exact block_closed034 i
 · exact block_closed035 i

theorem all_isomorphic_cases_closed (i : Fin 3600) : CoreExcluded (caseCore i) := by
 let b : Fin 36 := ⟨i.val/100,by omega⟩
 let j : Fin 100 := ⟨i.val%100,Nat.mod_lt _ (by decide)⟩
 have he : i=blockCase b j := by apply Fin.ext; dsimp [blockCase,b,j];omega
 rw [he]
 exact blocks_closed b j

theorem all_isomorphic_cores_excluded (x : Fin 2) (y : Fin 72) (g : Fin 25) : CoreExcluded (baseCore x y g) := by
 rw [←caseCore_index x y g]
 exact all_isomorphic_cases_closed _

#print axioms all_isomorphic_cores_excluded
end PricingC.GIsomorphic
