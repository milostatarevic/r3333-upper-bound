import PricingIntegration.NativePrimaryCore
import R4333Lean.FiniteColorCNF

namespace PricingIntegration.DNativeEdgeMap
open PricingIntegration.NativePrimaryCore
def row50 (i : Nat) : Nat := (if i < 925 then (if i < 522 then (if i < 279 then (if i < 144 then (if i < 49 then 0 else (if i < 97 then 1 else 2)) else (if i < 190 then 3 else (if i < 235 then 4 else 5))) else (if i < 405 then (if i < 322 then 6 else (if i < 364 then 7 else 8)) else (if i < 445 then 9 else (if i < 484 then 10 else 11)))) else (if i < 729 then (if i < 630 then (if i < 559 then 12 else (if i < 595 then 13 else 14)) else (if i < 664 then 15 else (if i < 697 then 16 else 17))) else (if i < 819 then (if i < 760 then 18 else (if i < 790 then 19 else 20)) else (if i < 874 then (if i < 847 then 21 else 22) else (if i < 900 then 23 else 24))))) else (if i < 1147 then (if i < 1054 then (if i < 994 then (if i < 949 then 25 else (if i < 972 then 26 else 27)) else (if i < 1015 then 28 else (if i < 1035 then 29 else 30))) else (if i < 1105 then (if i < 1072 then 31 else (if i < 1089 then 32 else 33)) else (if i < 1120 then 34 else (if i < 1134 then 35 else 36)))) else (if i < 1204 then (if i < 1180 then (if i < 1159 then 37 else (if i < 1170 then 38 else 39)) else (if i < 1189 then 40 else (if i < 1197 then 41 else 42))) else (if i < 1219 then (if i < 1210 then 43 else (if i < 1215 then 44 else 45)) else (if i < 1224 then (if i < 1222 then 46 else 47) else (if i < 1225 then 48 else 49))))))
def row51 (i : Nat) : Nat := (if i < 950 then (if i < 534 then (if i < 285 then (if i < 147 then (if i < 50 then 0 else (if i < 99 then 1 else 2)) else (if i < 194 then 3 else (if i < 240 then 4 else 5))) else (if i < 414 then (if i < 329 then 6 else (if i < 372 then 7 else 8)) else (if i < 455 then 9 else (if i < 495 then 10 else 11)))) else (if i < 747 then (if i < 645 then (if i < 572 then 12 else (if i < 609 then 13 else 14)) else (if i < 680 then 15 else (if i < 714 then 16 else 17))) else (if i < 840 then (if i < 779 then 18 else (if i < 810 then 19 else 20)) else (if i < 897 then (if i < 869 then 21 else 22) else (if i < 924 then 23 else 24))))) else (if i < 1197 then (if i < 1085 then (if i < 1022 then (if i < 975 then 25 else (if i < 999 then 26 else 27)) else (if i < 1044 then 28 else (if i < 1065 then 29 else 30))) else (if i < 1139 then (if i < 1104 then 31 else (if i < 1122 then 32 else 33)) else (if i < 1170 then (if i < 1155 then 34 else 35) else (if i < 1184 then 36 else 37)))) else (if i < 1254 then (if i < 1230 then (if i < 1209 then 38 else (if i < 1220 then 39 else 40)) else (if i < 1239 then 41 else (if i < 1247 then 42 else 43))) else (if i < 1269 then (if i < 1260 then 44 else (if i < 1265 then 45 else 46)) else (if i < 1274 then (if i < 1272 then 47 else 48) else (if i < 1275 then 49 else 50))))))
def sparse (n d : Nat) : Nat :=
  let i:=(d-1)/4
  let a:=if n=50 then row50 i else row51 i
  R4333.FiniteColorCNF.edgeAtom a (a+1+(i-rowStart n a)) ((d-1)%4)

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
theorem ordered_roundtrip50 : ∀u v : Fin 50,∀q : Fin 4,u<v →
  sparse 50 (orderedEdgeVar u v q)=R4333.FiniteColorCNF.edgeAtom u.val v.val q.val := by decide +kernel
#print axioms ordered_roundtrip50
theorem ordered_roundtrip51 : ∀u v : Fin 51,∀q : Fin 4,u<v →
  sparse 51 (orderedEdgeVar u v q)=R4333.FiniteColorCNF.edgeAtom u.val v.val q.val := by decide +kernel
#print axioms ordered_roundtrip51
end PricingIntegration.DNativeEdgeMap
