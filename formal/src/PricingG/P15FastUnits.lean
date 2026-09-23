import R4333Lean.ProfileDUUUFourSupportP15MatrixOnlyLeaves61
namespace PricingG.P15FastUnits
open R4333 FiniteColorCNF ProfileDTripleJoinReduction ProfileDFourSupportRestoredRootK15
open ProfileDDegreeTenMatrixLeafDataUUU2P15
open ProfileDUUUFourSupportP15SwapData61 ProfileDUUUFourSupportP15SwapFiniteCoverage61
open ProfileDUUUFourSupportP15MatrixOnlyLeaves61
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def firstData : Array (SupportRepresentative) := #[.s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s4, .s4, .s4, .s4, .s4, .s4,
    .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4,
    .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4]
def first (i : Fin 372) : SupportRepresentative := (firstData[i.val]?).getD .s0
theorem first_eq (i : Fin 372) : first i=orderedFirst i := by fin_cases i <;> rfl

def secondData : Array (SupportRepresentative) := #[.s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4,
    .s4, .s4, .s4, .s4, .s4, .s4, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s4, .s4, .s4, .s4,
    .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s4, .s0, .s0, .s0, .s0, .s0, .s0,
    .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s0, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1,
    .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s1, .s4, .s4, .s4, .s4]
def second (i : Fin 372) : SupportRepresentative := (secondData[i.val]?).getD .s0
theorem second_eq (i : Fin 372) : second i=orderedSecond i := by fin_cases i <;> rfl

def seedData : Array (Fin 372) := #[0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 28, 29, 35, 36, 40, 44, 45, 48, 49, 52, 55, 56, 72, 76, 77, 78, 79, 80, 81, 82, 83, 84,
    85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105,
    106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123,
    124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141,
    142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159,
    160, 161, 162, 163, 164, 165, 166, 167, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253,
    254, 255, 256, 258, 259, 260, 262, 264, 265, 266, 268, 269, 271, 272, 274, 276, 277, 280,
    281, 283, 284, 287, 289, 293, 295, 296, 299, 310, 315, 320, 321, 322, 323, 324, 325, 326,
    327, 328, 329, 330, 331, 332, 333, 334, 335, 368, 369, 371]
def seed (i : Fin 189) : Fin 372 := (seedData[i.val]?).getD 0
theorem seed_eq (i : Fin 189) : seed i=seedLeaf i := by fin_cases i <;> rfl


def physical (leaf : Fin 372) (i : Fin 14) : ProfileDFourRowCNF.TotalVertex :=
  match fourFiveFiveEquiv.symm i with
  | .inl (.inl free) => ProfileDFourRowCNF.freeVertex free
  | .inl (.inr p) => ProfileDFourRowCNF.tailVertex
      (blockVertex 0 ((support (first leaf)).embedding p).val)
  | .inr p => ProfileDFourRowCNF.tailVertex
      (blockVertex 1 ((support (second leaf)).embedding p).val)

theorem physical_eq (leaf : Fin 372) (i : Fin 14) :
    physical leaf i=leafPhysicalVertex leaf i := by
  simp only [physical,leafPhysicalVertex,first_eq,second_eq]
  rfl

def units (i : Fin 189) : Sat.Fmla :=
  (edges 14).map fun pair =>
    let a := ProfileDUUUFourSupportP15MatrixOnlyLeaves61.matrixIndex pair.1
    let b := ProfileDUUUFourSupportP15MatrixOnlyLeaves61.matrixIndex pair.2
    [Sat.Literal.pos (edgeAtom (physical (seed i) a).val (physical (seed i) b).val
      (orderedMatrixColor (seed i) a b).val)]

theorem units_eq (i : Fin 189) : units i=matrixUnitFmla (seedLeaf i) := by
  simp only [units,seed_eq,physical_eq,matrixUnitFmla,ProfileDUUUFourSupportP15MatrixOnlyLeaves61.matrixUnitClause]
  rfl
#print axioms units_eq
end PricingG.P15FastUnits
