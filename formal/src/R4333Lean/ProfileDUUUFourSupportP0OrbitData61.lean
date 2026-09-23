import R4333Lean.ProfileDUUUFourSupportP0SelectorBridge61
import R4333Lean.RootForbiddenK4FreeVertexOrbits

/-! Concrete finite data for restored-root K15 matrix orbit coverage. -/
namespace R4333
namespace ProfileDUUUFourSupportP0OrbitData61

open SingleRootStarCNF
open ProfileDUUUDegreeTenCatalogOrbits61
open ProfileDUUUFourSupportP0RepresentativeData61
open ProfileDFourSupportRestoredRootK15

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

abbrev RootCase := Fin 10
abbrev FreeLabelAction := Fin 24
abbrev CandidateIndex := Fin 24000

def rootTwisted : RootCase → Bool := ![false, false, false, false, false, true, true, true, true, true]
def rootVertex : RootCase → Fin 15 := ![0, 3, 5, 7, 14, 0, 3, 5, 7, 14]

def rootFreeGroupVertex : RootCase → Fin 4 → Fin 15 :=
  ![![1, 8, 10, 12],
    ![2, 9, 11, 12],
    ![4, 9, 10, 13],
    ![6, 8, 11, 13],
    ![1, 2, 4, 6],
    ![1, 8, 10, 12],
    ![2, 9, 11, 12],
    ![4, 9, 10, 13],
    ![6, 8, 11, 13],
    ![1, 2, 4, 6]]
def rootFirstGroupVertex : RootCase → Fin 5 → Fin 15 :=
  ![![2, 3, 7, 11, 13],
    ![0, 1, 4, 8, 14],
    ![2, 6, 7, 8, 14],
    ![0, 4, 5, 10, 12],
    ![3, 5, 9, 12, 13],
    ![2, 3, 7, 11, 13],
    ![0, 1, 4, 8, 14],
    ![1, 6, 7, 11, 14],
    ![0, 4, 5, 10, 12],
    ![3, 5, 9, 12, 13]]
def rootSecondGroupVertex : RootCase → Fin 5 → Fin 15 :=
  ![![4, 5, 6, 9, 14],
    ![5, 6, 7, 10, 13],
    ![0, 1, 3, 11, 12],
    ![1, 2, 3, 9, 14],
    ![0, 7, 8, 10, 11],
    ![4, 5, 6, 9, 14],
    ![5, 6, 7, 10, 13],
    ![0, 2, 3, 8, 12],
    ![1, 2, 3, 9, 14],
    ![0, 7, 8, 10, 11]]

def rootFreeGroupPosition : RootCase → Fin 15 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 3, 0],
    ![0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 2, 3, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 2, 0, 3, 0],
    ![0, 0, 1, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0]]
def rootFirstGroupPosition : RootCase → Fin 15 → Fin 5 :=
  ![![0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 4, 0],
    ![0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 3, 4, 0],
    ![0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 4, 0],
    ![0, 1, 0, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 4],
    ![0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 4, 0, 0],
    ![0, 0, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0, 3, 4, 0]]
def rootSecondGroupPosition : RootCase → Fin 15 → Fin 5 :=
  ![![0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 4, 0],
    ![0, 1, 0, 2, 0, 0, 0, 0, 0, 0, 0, 3, 4, 0, 0],
    ![0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 4, 0, 0, 0],
    ![0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 3, 0, 0, 4, 0],
    ![0, 0, 1, 2, 0, 0, 0, 0, 3, 0, 0, 0, 4, 0, 0],
    ![0, 0, 1, 2, 0, 0, 0, 0, 0, 3, 0, 0, 0, 0, 4],
    ![0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 4, 0, 0, 0]]

def freeLabelPermutation : FreeLabelAction → Fin 4 → Fin 4 :=
  ![![0, 1, 2, 3],
    ![0, 1, 3, 2],
    ![0, 2, 1, 3],
    ![0, 2, 3, 1],
    ![0, 3, 1, 2],
    ![0, 3, 2, 1],
    ![1, 0, 2, 3],
    ![1, 0, 3, 2],
    ![1, 2, 0, 3],
    ![1, 2, 3, 0],
    ![1, 3, 0, 2],
    ![1, 3, 2, 0],
    ![2, 0, 1, 3],
    ![2, 0, 3, 1],
    ![2, 1, 0, 3],
    ![2, 1, 3, 0],
    ![2, 3, 0, 1],
    ![2, 3, 1, 0],
    ![3, 0, 1, 2],
    ![3, 0, 2, 1],
    ![3, 1, 0, 2],
    ![3, 1, 2, 0],
    ![3, 2, 0, 1],
    ![3, 2, 1, 0]]

def firstCompatiblePerm0 : RootCase → Fin 10 → Fin 5 → Fin 5 :=
  ![![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 1, 2, 3, 4],
      ![0, 3, 4, 1, 2],
      ![1, 0, 2, 4, 3],
      ![1, 4, 3, 0, 2],
      ![2, 3, 1, 4, 0],
      ![2, 4, 0, 3, 1],
      ![3, 0, 4, 2, 1],
      ![3, 2, 1, 0, 4],
      ![4, 1, 3, 2, 0],
      ![4, 2, 0, 1, 3]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]],
    ![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 1, 2, 3, 4],
      ![0, 3, 4, 1, 2],
      ![1, 0, 2, 4, 3],
      ![1, 4, 3, 0, 2],
      ![2, 3, 1, 4, 0],
      ![2, 4, 0, 3, 1],
      ![3, 0, 4, 2, 1],
      ![3, 2, 1, 0, 4],
      ![4, 1, 3, 2, 0],
      ![4, 2, 0, 1, 3]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]]]

def firstCompatiblePerm2 : RootCase → Fin 10 → Fin 5 → Fin 5 :=
  ![![![0, 2, 1, 3, 4],
      ![0, 3, 4, 2, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 0, 3, 1, 4],
      ![2, 1, 4, 0, 3],
      ![3, 0, 2, 4, 1],
      ![3, 4, 1, 0, 2],
      ![4, 1, 2, 3, 0],
      ![4, 3, 0, 1, 2]],
    ![![0, 2, 1, 4, 3],
      ![0, 4, 3, 2, 1],
      ![1, 2, 0, 3, 4],
      ![1, 3, 4, 2, 0],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 0, 2, 3, 1],
      ![4, 3, 1, 0, 2]],
    ![![0, 1, 3, 2, 4],
      ![0, 2, 4, 1, 3],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 0, 1, 4, 3],
      ![2, 4, 3, 0, 1],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 2, 0, 3, 1],
      ![4, 3, 1, 2, 0]],
    ![![0, 1, 3, 2, 4],
      ![0, 2, 4, 1, 3],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 0, 1, 4, 3],
      ![2, 4, 3, 0, 1],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 2, 0, 3, 1],
      ![4, 3, 1, 2, 0]],
    ![![0, 1, 3, 4, 2],
      ![0, 4, 2, 1, 3],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 3, 1, 4, 0],
      ![2, 4, 0, 3, 1],
      ![3, 1, 0, 2, 4],
      ![3, 2, 4, 1, 0],
      ![4, 0, 1, 2, 3],
      ![4, 2, 3, 0, 1]],
    ![![0, 2, 1, 3, 4],
      ![0, 3, 4, 2, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 0, 3, 1, 4],
      ![2, 1, 4, 0, 3],
      ![3, 0, 2, 4, 1],
      ![3, 4, 1, 0, 2],
      ![4, 1, 2, 3, 0],
      ![4, 3, 0, 1, 2]],
    ![![0, 2, 1, 4, 3],
      ![0, 4, 3, 2, 1],
      ![1, 2, 0, 3, 4],
      ![1, 3, 4, 2, 0],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 0, 2, 3, 1],
      ![4, 3, 1, 0, 2]],
    ![![0, 1, 3, 2, 4],
      ![0, 2, 4, 1, 3],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 0, 1, 4, 3],
      ![2, 4, 3, 0, 1],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 2, 0, 3, 1],
      ![4, 3, 1, 2, 0]],
    ![![0, 1, 3, 2, 4],
      ![0, 2, 4, 1, 3],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 0, 1, 4, 3],
      ![2, 4, 3, 0, 1],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 2, 0, 3, 1],
      ![4, 3, 1, 2, 0]],
    ![![0, 1, 3, 4, 2],
      ![0, 4, 2, 1, 3],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 3, 1, 4, 0],
      ![2, 4, 0, 3, 1],
      ![3, 1, 0, 2, 4],
      ![3, 2, 4, 1, 0],
      ![4, 0, 1, 2, 3],
      ![4, 2, 3, 0, 1]]]

def firstCompatiblePerm7 : RootCase → Fin 10 → Fin 5 → Fin 5 :=
  ![![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]],
    ![![0, 2, 3, 4, 1],
      ![0, 4, 1, 2, 3],
      ![1, 2, 4, 3, 0],
      ![1, 3, 0, 2, 4],
      ![2, 0, 3, 1, 4],
      ![2, 1, 4, 0, 3],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 0, 1, 3, 2],
      ![4, 3, 2, 0, 1]],
    ![![0, 1, 4, 2, 3],
      ![0, 2, 3, 1, 4],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 0, 3, 4, 1],
      ![2, 4, 1, 0, 3],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 2, 1, 3, 0],
      ![4, 3, 0, 2, 1]],
    ![![0, 1, 4, 2, 3],
      ![0, 2, 3, 1, 4],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 0, 3, 4, 1],
      ![2, 4, 1, 0, 3],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 2, 1, 3, 0],
      ![4, 3, 0, 2, 1]],
    ![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]],
    ![![0, 2, 3, 4, 1],
      ![0, 4, 1, 2, 3],
      ![1, 2, 4, 3, 0],
      ![1, 3, 0, 2, 4],
      ![2, 0, 3, 1, 4],
      ![2, 1, 4, 0, 3],
      ![3, 1, 0, 4, 2],
      ![3, 4, 2, 1, 0],
      ![4, 0, 1, 3, 2],
      ![4, 3, 2, 0, 1]],
    ![![0, 1, 4, 2, 3],
      ![0, 2, 3, 1, 4],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 0, 3, 4, 1],
      ![2, 4, 1, 0, 3],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 2, 1, 3, 0],
      ![4, 3, 0, 2, 1]],
    ![![0, 1, 4, 2, 3],
      ![0, 2, 3, 1, 4],
      ![1, 0, 4, 3, 2],
      ![1, 3, 2, 0, 4],
      ![2, 0, 3, 4, 1],
      ![2, 4, 1, 0, 3],
      ![3, 1, 2, 4, 0],
      ![3, 4, 0, 1, 2],
      ![4, 2, 1, 3, 0],
      ![4, 3, 0, 2, 1]],
    ![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]]]

def firstCompatiblePerm : SupportKind → RootCase → Fin 10 → Fin 5 → Fin 5
  | .support0 => firstCompatiblePerm0
  | .support2 => firstCompatiblePerm2
  | .support7 => firstCompatiblePerm7

def secondCompatiblePerm : RootCase → Fin 10 → Fin 5 → Fin 5 :=
  ![![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 3, 2, 4, 1],
      ![0, 4, 1, 3, 2],
      ![1, 2, 0, 3, 4],
      ![1, 3, 4, 2, 0],
      ![2, 1, 0, 4, 3],
      ![2, 4, 3, 1, 0],
      ![3, 0, 2, 1, 4],
      ![3, 1, 4, 0, 2],
      ![4, 0, 1, 2, 3],
      ![4, 2, 3, 0, 1]],
    ![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]],
    ![![0, 1, 2, 4, 3],
      ![0, 4, 3, 1, 2],
      ![1, 0, 2, 3, 4],
      ![1, 3, 4, 0, 2],
      ![2, 3, 0, 4, 1],
      ![2, 4, 1, 3, 0],
      ![3, 1, 4, 2, 0],
      ![3, 2, 0, 1, 4],
      ![4, 0, 3, 2, 1],
      ![4, 2, 1, 0, 3]],
    ![![0, 3, 2, 4, 1],
      ![0, 4, 1, 3, 2],
      ![1, 2, 0, 3, 4],
      ![1, 3, 4, 2, 0],
      ![2, 1, 0, 4, 3],
      ![2, 4, 3, 1, 0],
      ![3, 0, 2, 1, 4],
      ![3, 1, 4, 0, 2],
      ![4, 0, 1, 2, 3],
      ![4, 2, 3, 0, 1]],
    ![![0, 3, 2, 4, 1],
      ![0, 4, 1, 3, 2],
      ![1, 2, 0, 3, 4],
      ![1, 3, 4, 2, 0],
      ![2, 1, 0, 4, 3],
      ![2, 4, 3, 1, 0],
      ![3, 0, 2, 1, 4],
      ![3, 1, 4, 0, 2],
      ![4, 0, 1, 2, 3],
      ![4, 2, 3, 0, 1]],
    ![![0, 3, 1, 4, 2],
      ![0, 4, 2, 3, 1],
      ![1, 2, 0, 4, 3],
      ![1, 4, 3, 2, 0],
      ![2, 1, 0, 3, 4],
      ![2, 3, 4, 1, 0],
      ![3, 0, 1, 2, 4],
      ![3, 2, 4, 0, 1],
      ![4, 0, 2, 1, 3],
      ![4, 1, 3, 0, 2]],
    ![![0, 2, 4, 3, 1],
      ![0, 3, 1, 2, 4],
      ![1, 2, 3, 4, 0],
      ![1, 4, 0, 2, 3],
      ![2, 0, 4, 1, 3],
      ![2, 1, 3, 0, 4],
      ![3, 0, 1, 4, 2],
      ![3, 4, 2, 0, 1],
      ![4, 1, 0, 3, 2],
      ![4, 3, 2, 1, 0]]]

def matrixCoordinate : Fin 14 → FourFiveFiveCoordinates :=
  ![.inl (.inl 0), .inl (.inl 1), .inl (.inl 2), .inl (.inl 3),
    .inl (.inr 0), .inl (.inr 1), .inl (.inr 2), .inl (.inr 3),
    .inl (.inr 4), .inr 0, .inr 1, .inr 2, .inr 3, .inr 4]

def matrixCoordinateIndex : FourFiveFiveCoordinates → Fin 14
  | .inl (.inl a) => ⟨a.val, by omega⟩
  | .inl (.inr a) => ⟨4 + a.val, by omega⟩
  | .inr a => ⟨9 + a.val, by omega⟩

@[simp] theorem matrixCoordinate_index (p : FourFiveFiveCoordinates) :
    matrixCoordinate (matrixCoordinateIndex p) = p := by
  rcases p with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · fin_cases freePosition <;> rfl
    · fin_cases firstPosition <;> rfl
  · fin_cases secondPosition <;> rfl

@[simp] theorem matrixCoordinateIndex_coordinate (p : Fin 14) :
    matrixCoordinateIndex (matrixCoordinate p) = p := by
  fin_cases p <;> rfl

theorem matrixCoordinate_eq_equiv_symm (p : Fin 14) :
    matrixCoordinate p = fourFiveFiveEquiv.symm p := by
  fin_cases p <;> decide

def candidateVertex (kind : SupportKind) (root : RootCase)
    (free : FreeLabelAction) (first second : Fin 10) : Fin 14 → Fin 15 :=
  fun p => match matrixCoordinate p with
    | .inl (.inl a) =>
        rootFreeGroupVertex root (freeLabelPermutation free a)
    | .inl (.inr a) =>
        rootFirstGroupVertex root (firstCompatiblePerm kind root first a)
    | .inr a =>
        rootSecondGroupVertex root (secondCompatiblePerm root second a)

def candidateColor (kind : SupportKind) (root : RootCase)
    (free : FreeLabelAction) (first second : Fin 10)
    (left right : Fin 14) : Fin 4 :=
  canonicalPalette 1 (k15Template (rootTwisted root)
    (candidateVertex kind root free first second left)
    (candidateVertex kind root free first second right))

/-- Array form used only by the finite kernel check. -/
def checkedCandidateVertex (kind : SupportKind) (root : RootCase)
    (free : FreeLabelAction) (first second : Fin 10) : Fin 14 → Fin 15 :=
  ![rootFreeGroupVertex root (freeLabelPermutation free 0),
    rootFreeGroupVertex root (freeLabelPermutation free 1),
    rootFreeGroupVertex root (freeLabelPermutation free 2),
    rootFreeGroupVertex root (freeLabelPermutation free 3),
    rootFirstGroupVertex root (firstCompatiblePerm kind root first 0),
    rootFirstGroupVertex root (firstCompatiblePerm kind root first 1),
    rootFirstGroupVertex root (firstCompatiblePerm kind root first 2),
    rootFirstGroupVertex root (firstCompatiblePerm kind root first 3),
    rootFirstGroupVertex root (firstCompatiblePerm kind root first 4),
    rootSecondGroupVertex root (secondCompatiblePerm root second 0),
    rootSecondGroupVertex root (secondCompatiblePerm root second 1),
    rootSecondGroupVertex root (secondCompatiblePerm root second 2),
    rootSecondGroupVertex root (secondCompatiblePerm root second 3),
    rootSecondGroupVertex root (secondCompatiblePerm root second 4)]

def checkedCandidateColor (kind : SupportKind) (root : RootCase)
    (free : FreeLabelAction) (first second : Fin 10)
    (left right : Fin 14) : Fin 4 :=
  canonicalPalette 1 (k15Template (rootTwisted root)
    (checkedCandidateVertex kind root free first second left)
    (checkedCandidateVertex kind root free first second right))

def orbitCoordinate (kind : SupportKind) (free : FreeLabelAction)
    (first second : Fin 10) : Fin 14 → Fin 14 :=
  fun p => matrixCoordinateIndex <| match matrixCoordinate p with
    | .inl (.inl a) => .inl (.inl (freeLabelPermutation free a))
    | .inl (.inr a) => .inl (.inr (u15Action kind first a))
    | .inr a => .inr (u16Action second a)

def checkedOrbitCoordinate (kind : SupportKind) (free : FreeLabelAction)
    (first second : Fin 10) : Fin 14 → Fin 14 :=
  ![⟨(freeLabelPermutation free 0).val, by omega⟩,
    ⟨(freeLabelPermutation free 1).val, by omega⟩,
    ⟨(freeLabelPermutation free 2).val, by omega⟩,
    ⟨(freeLabelPermutation free 3).val, by omega⟩,
    ⟨4 + (u15Action kind first 0).val, by omega⟩,
    ⟨4 + (u15Action kind first 1).val, by omega⟩,
    ⟨4 + (u15Action kind first 2).val, by omega⟩,
    ⟨4 + (u15Action kind first 3).val, by omega⟩,
    ⟨4 + (u15Action kind first 4).val, by omega⟩,
    ⟨9 + (u16Action second 0).val, by omega⟩,
    ⟨9 + (u16Action second 1).val, by omega⟩,
    ⟨9 + (u16Action second 2).val, by omega⟩,
    ⟨9 + (u16Action second 3).val, by omega⟩,
    ⟨9 + (u16Action second 4).val, by omega⟩]

@[simp] theorem fourFiveFive_free_val (a : Fin 4) :
    (fourFiveFiveEquiv (.inl (.inl a))).val = a.val := by
  simp only [fourFiveFiveEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    finSumFinEquiv_apply_left]
  rfl

@[simp] theorem fourFiveFive_first_val (a : Fin 5) :
    (fourFiveFiveEquiv (.inl (.inr a))).val = 4 + a.val := by
  simp only [fourFiveFiveEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]
  rfl

@[simp] theorem fourFiveFive_second_val (a : Fin 5) :
    (fourFiveFiveEquiv (.inr a)).val = 9 + a.val := by
  simp only [fourFiveFiveEquiv, Equiv.trans_apply, Equiv.sumCongr_apply,
    finSumFinEquiv_apply_right]
  rfl

theorem matrixCoordinateIndex_eq_equiv (p : FourFiveFiveCoordinates) :
    matrixCoordinateIndex p = fourFiveFiveEquiv p := by
  rcases p with (left | secondPosition)
  · rcases left with (freePosition | firstPosition)
    · apply Fin.ext
      exact (fourFiveFive_free_val freePosition).symm
    · apply Fin.ext
      exact (fourFiveFive_first_val firstPosition).symm
  · apply Fin.ext
    exact (fourFiveFive_second_val secondPosition).symm

@[simp] theorem fourFiveFive_free_eq (a : Fin 4) :
    fourFiveFiveEquiv (.inl (.inl a)) =
      (⟨a.val, by omega⟩ : Fin 14) := by
  apply Fin.ext
  exact fourFiveFive_free_val a

@[simp] theorem fourFiveFive_first_eq (a : Fin 5) :
    fourFiveFiveEquiv (.inl (.inr a)) =
      (⟨4 + a.val, by omega⟩ : Fin 14) := by
  apply Fin.ext
  exact fourFiveFive_first_val a

@[simp] theorem fourFiveFive_second_eq (a : Fin 5) :
    fourFiveFiveEquiv (.inr a) =
      (⟨9 + a.val, by omega⟩ : Fin 14) := by
  apply Fin.ext
  exact fourFiveFive_second_val a

@[simp] theorem fourFiveFive_symm_free_eq (a : Fin 4) :
    fourFiveFiveEquiv.symm (⟨a.val, by omega⟩ : Fin 14) =
      .inl (.inl a) := by
  rw [← fourFiveFive_free_eq a]
  exact fourFiveFiveEquiv.symm_apply_apply _

@[simp] theorem fourFiveFive_symm_first_eq (a : Fin 5) :
    fourFiveFiveEquiv.symm (⟨4 + a.val, by omega⟩ : Fin 14) =
      .inl (.inr a) := by
  rw [← fourFiveFive_first_eq a]
  exact fourFiveFiveEquiv.symm_apply_apply _

@[simp] theorem fourFiveFive_symm_second_eq (a : Fin 5) :
    fourFiveFiveEquiv.symm (⟨9 + a.val, by omega⟩ : Fin 14) =
      .inr a := by
  rw [← fourFiveFive_second_eq a]
  exact fourFiveFiveEquiv.symm_apply_apply _

theorem checkedCandidateVertex_eq_candidateVertex
    (kind : SupportKind) (root : RootCase) (free : FreeLabelAction)
    (first second : Fin 10) (p : Fin 14) :
    checkedCandidateVertex kind root free first second p =
      candidateVertex kind root free first second p := by
  fin_cases p <;> rfl

theorem checkedOrbitCoordinate_eq_orbitCoordinate
    (kind : SupportKind) (free : FreeLabelAction)
    (first second : Fin 10) (p : Fin 14) :
    checkedOrbitCoordinate kind free first second p =
      orbitCoordinate kind free first second p := by
  fin_cases p <;> rfl

theorem checkedCandidateColor_eq_candidateColor
    (kind : SupportKind) (root : RootCase) (free : FreeLabelAction)
    (first second : Fin 10) (left right : Fin 14) :
    checkedCandidateColor kind root free first second left right =
      candidateColor kind root free first second left right := by
  unfold checkedCandidateColor candidateColor
  rw [checkedCandidateVertex_eq_candidateVertex,
    checkedCandidateVertex_eq_candidateVertex]

def supportKindPair : SupportKind → SupportPair
  | .support0 => 0
  | .support2 => 1
  | .support7 => 2

def candidateRoot (i : CandidateIndex) : RootCase := ⟨i.val / 2400, by omega⟩
def candidateFree (i : CandidateIndex) : FreeLabelAction := ⟨(i.val / 100) % 24, by omega⟩
def candidateFirst (i : CandidateIndex) : Fin 10 := ⟨(i.val / 10) % 10, by omega⟩
def candidateSecond (i : CandidateIndex) : Fin 10 := ⟨i.val % 10, by omega⟩

/-! ## Factorized normalization of the 24 x 10 x 10 label choices -/

def freeNormalizerAction : FreeLabelAction → FreeLabelAction :=
  ![0, 1, 2, 4, 3, 5, 6, 7, 12, 18, 13, 19, 8, 10, 14, 20, 16, 22, 9, 11, 15, 21, 17, 23]

def firstReduced0 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 3, 3, 1, 0, 7, 2, 7],
    ![0, 1, 2, 3, 1, 3, 2, 7, 0, 7],
    ![0, 1, 2, 1, 4, 0, 6, 2, 6, 4],
    ![0, 1, 2, 1, 4, 0, 6, 2, 6, 4],
    ![0, 1, 0, 3, 4, 5, 4, 3, 5, 1],
    ![0, 1, 2, 3, 3, 1, 0, 7, 2, 7],
    ![0, 1, 2, 3, 1, 3, 2, 7, 0, 7],
    ![0, 1, 2, 1, 4, 0, 6, 2, 6, 4],
    ![0, 1, 2, 1, 4, 0, 6, 2, 6, 4],
    ![0, 1, 0, 3, 4, 5, 4, 3, 5, 1]]
def firstNormalizerAction0 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 0, 1, 1, 1, 0, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 0, 1, 0, 1, 0, 1, 1, 1],
    ![0, 0, 1, 0, 0, 0, 1, 1, 1, 1]]

def firstReduced2 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8],
    ![0, 0, 2, 2, 4, 4, 6, 6, 8, 8]]
def firstNormalizerAction2 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
    ![0, 1, 0, 1, 0, 1, 0, 1, 0, 1]]

def firstReduced7 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
def firstNormalizerAction7 : RootCase → Fin 10 → Fin 10 :=
  ![![0, 1, 8, 4, 2, 6, 3, 7, 5, 9],
    ![0, 1, 8, 4, 2, 6, 5, 9, 3, 7],
    ![0, 1, 2, 6, 3, 7, 8, 4, 9, 5],
    ![0, 1, 2, 6, 3, 7, 8, 4, 9, 5],
    ![0, 1, 2, 6, 5, 9, 8, 4, 3, 7],
    ![0, 1, 8, 4, 2, 6, 3, 7, 5, 9],
    ![0, 1, 8, 4, 2, 6, 5, 9, 3, 7],
    ![0, 1, 2, 6, 3, 7, 8, 4, 9, 5],
    ![0, 1, 2, 6, 3, 7, 8, 4, 9, 5],
    ![0, 1, 2, 6, 5, 9, 8, 4, 3, 7]]

def firstReduced : SupportKind → RootCase → Fin 10 → Fin 10
  | .support0 => firstReduced0
  | .support2 => firstReduced2
  | .support7 => firstReduced7

def firstNormalizerAction : SupportKind → RootCase → Fin 10 → Fin 10
  | .support0 => firstNormalizerAction0
  | .support2 => firstNormalizerAction2
  | .support7 => firstNormalizerAction7

def secondNormalizerAction : RootCase → Fin 10 → Fin 10 :=
  ![![0, 1, 2, 6, 5, 9, 8, 4, 3, 7],
    ![0, 1, 4, 8, 5, 9, 2, 6, 3, 7],
    ![0, 1, 2, 6, 5, 9, 8, 4, 3, 7],
    ![0, 1, 5, 9, 4, 8, 2, 6, 3, 7],
    ![0, 1, 8, 4, 2, 6, 3, 7, 5, 9],
    ![0, 1, 2, 6, 5, 9, 8, 4, 3, 7],
    ![0, 1, 4, 8, 5, 9, 2, 6, 3, 7],
    ![0, 1, 4, 8, 5, 9, 2, 6, 3, 7],
    ![0, 1, 5, 9, 4, 8, 2, 6, 3, 7],
    ![0, 1, 8, 4, 2, 6, 3, 7, 5, 9]]

theorem freeNormalizer_equation (a : FreeLabelAction) (p : Fin 4) :
    freeLabelPermutation a (freeLabelPermutation (freeNormalizerAction a) p) = p := by
  fin_cases a <;> fin_cases p <;> decide

theorem firstNormalizer_equation (kind : SupportKind) (root : RootCase)
    (a : Fin 10) (p : Fin 5) :
    firstCompatiblePerm kind root a
        (u15Action kind (firstNormalizerAction kind root a) p) =
      firstCompatiblePerm kind root (firstReduced kind root a) p := by
  cases kind <;> fin_cases root <;> fin_cases a <;> fin_cases p <;> decide

theorem secondNormalizer_equation (root : RootCase) (a : Fin 10) (p : Fin 5) :
    secondCompatiblePerm root a (u16Action (secondNormalizerAction root a) p) =
      secondCompatiblePerm root 0 p := by
  fin_cases root <;> fin_cases a <;> fin_cases p <;> decide

def reducedCandidateIndex (root : RootCase) (first : Fin 10) : CandidateIndex :=
  ⟨root.val * 2400 + first.val * 10, by omega⟩

#print axioms freeNormalizer_equation
#print axioms firstNormalizer_equation
#print axioms secondNormalizer_equation

theorem rootFreeGroupVertex_injective (root : RootCase) :
    Function.Injective (rootFreeGroupVertex root) := by fin_cases root <;> decide
theorem rootFirstGroupVertex_injective (root : RootCase) :
    Function.Injective (rootFirstGroupVertex root) := by fin_cases root <;> decide
theorem rootSecondGroupVertex_injective (root : RootCase) :
    Function.Injective (rootSecondGroupVertex root) := by fin_cases root <;> decide
@[simp] theorem rootFreeGroupPosition_vertex (root : RootCase) (p : Fin 4) :
    rootFreeGroupPosition root (rootFreeGroupVertex root p) = p := by fin_cases root <;> fin_cases p <;> decide
@[simp] theorem rootFirstGroupPosition_vertex (root : RootCase) (p : Fin 5) :
    rootFirstGroupPosition root (rootFirstGroupVertex root p) = p := by fin_cases root <;> fin_cases p <;> decide
@[simp] theorem rootSecondGroupPosition_vertex (root : RootCase) (p : Fin 5) :
    rootSecondGroupPosition root (rootSecondGroupVertex root p) = p := by fin_cases root <;> fin_cases p <;> decide
theorem rootFreeGroupVertex_position_of_color (root : RootCase) (v : Fin 15)
    (hne : v ≠ rootVertex root) (hcolor : k15Template (rootTwisted root) (rootVertex root) v = 0) :
    rootFreeGroupVertex root (rootFreeGroupPosition root v) = v := by
  fin_cases root <;> fin_cases v <;> (revert hne hcolor; decide)
theorem rootFirstGroupVertex_position_of_color (root : RootCase) (v : Fin 15)
    (hne : v ≠ rootVertex root) (hcolor : k15Template (rootTwisted root) (rootVertex root) v = 1) :
    rootFirstGroupVertex root (rootFirstGroupPosition root v) = v := by
  fin_cases root <;> fin_cases v <;> (revert hne hcolor; decide)
theorem rootSecondGroupVertex_position_of_color (root : RootCase) (v : Fin 15)
    (hne : v ≠ rootVertex root) (hcolor : k15Template (rootTwisted root) (rootVertex root) v = 2) :
    rootSecondGroupVertex root (rootSecondGroupPosition root v) = v := by
  fin_cases root <;> fin_cases v <;> (revert hne hcolor; decide)
theorem freeLabelPermutation_bijective (a : FreeLabelAction) :
    Function.Bijective (freeLabelPermutation a) := by fin_cases a <;> decide
@[simp] theorem freeLabelPermutation_zero (p : Fin 4) :
    freeLabelPermutation 0 p = p := by fin_cases p <;> decide

#print axioms rootFreeGroupVertex_position_of_color
#print axioms rootFirstGroupVertex_position_of_color
#print axioms rootSecondGroupVertex_position_of_color

end ProfileDUUUFourSupportP0OrbitData61
end R4333
