import R4333Lean.ContinuationDegreeNineTwistedRoot12QuotientFormula61
namespace PricingG.D9Root12Fast
open R4333 ContinuationDegreeNineTwistedRoot12QuotientFormula61
open ContinuationDegreeNineTwistedRoot12FactorOrbitCoverage61 ContinuationDegreeNineTwistedRoot12CaseFactorCNF61
open ContinuationDegreeNineTwistedRoot12CaseCNF61 ProfileDHighOwnFiveSupportC5CNF
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def pairData : Array (Fin 11 × Fin 12) := #[(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11),
    (2, 0), (2, 1), (2, 2), (2, 3), (2, 4), (2, 5),
    (2, 6), (2, 7), (2, 8), (2, 9), (2, 10), (2, 11),
    (4, 0), (4, 2), (4, 4), (4, 5), (4, 7), (4, 9),
    (4, 10), (4, 11),
    (5, 0), (5, 1), (5, 2), (5, 3), (5, 4), (5, 5),
    (5, 6), (5, 7), (5, 8), (5, 9), (5, 10), (5, 11),
    (6, 0), (6, 1), (6, 2), (6, 3), (6, 4), (6, 5),
    (6, 6), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11),
    (8, 0), (8, 2), (8, 4), (8, 5), (8, 7), (8, 9),
    (8, 10), (8, 11),
    (10, 0), (10, 2), (10, 4), (10, 5), (10, 7), (10, 9),
    (10, 10), (10, 11)]
def pair (i : Fin 72) : Fin 11 × Fin 12 := pairData[i.val]!
theorem pair_eq (i : Fin 72) : pair i = quotientRepresentativePair i := by fin_cases i <;> rfl

def smallMaskData : Array (Nat) := #[1031, 8199, 2059, 4107, 9219, 6147, 269, 9221, 6153, 1409,
    2433, 3201, 12417, 3329, 526, 16398, 16902, 9222, 16906, 6154,
    1602, 2626, 3138, 12354, 20546, 24642, 3586, 28674, 16908, 804,
    1316, 1572, 24612, 1796, 792, 2328, 2584, 20504, 2824, 624,
    16496, 432, 16944, 2256, 4304, 16976, 6224, 6288, 2832, 1248,
    8416, 16992, 9312, 9376, 1824, 9408, 6336, 3648, 28736, 3456]
def smallMask (i : Fin 60) : Nat := smallMaskData[i.val]!
theorem smallMask_eq (i : Fin 60) : smallMask i = indexedSmallMask i := by fin_cases i <;> rfl

def largeMaskData : Array (Nat) := #[9223, 6155, 3457, 16910, 3650, 28738, 1828, 2840, 17008, 6352, 9440]
def largeMask (i : Fin 11) : Nat := largeMaskData[i.val]!
theorem largeMask_eq (i : Fin 11) : largeMask i = indexedLargeMask i := by fin_cases i <;> rfl

def largePhysicalData : Array (Array (Fin 15)) := #[#[0, 2, 10, 13, 1], #[1, 2, 13, 10, 0],
    #[1, 10, 0, 2, 13], #[2, 1, 13, 0, 10],
    #[2, 0, 10, 1, 13], #[0, 3, 12, 11, 1],
    #[0, 11, 1, 3, 12], #[1, 3, 11, 12, 0],
    #[1, 12, 0, 3, 11], #[12, 1, 0, 11, 3],
    #[1, 6, 9, 10, 11]]
def largePhysical (i : Fin 11) (j : Fin 5) : Fin 15 := (largePhysicalData[i.val]!)[j.val]!
theorem largePhysical_eq (i : Fin 11) (j : Fin 5) : largePhysical i j=quotientLargePhysicalTable i j := by fin_cases i <;> fin_cases j <;> rfl

def smallPhysicalData : Array (Array (Fin 15)) := #[#[0, 2, 10, 1], #[10, 1, 0, 2],
    #[1, 2, 13, 0], #[13, 0, 1, 2],
    #[1, 3, 11, 0], #[0, 3, 12, 1],
    #[12, 1, 0, 3], #[0, 11, 1, 12],
    #[1, 12, 0, 11], #[2, 0, 8, 3],
    #[2, 1, 13, 10], #[6, 1, 9, 10]]
def smallPhysical (i : Fin 12) (j : Fin 4) : Fin 15 := (smallPhysicalData[i.val]!)[j.val]!
theorem smallPhysical_eq (i : Fin 12) (j : Fin 4) : smallPhysical i j=quotientSmallPhysicalTable i j := by fin_cases i <;> fin_cases j <;> rfl


def edge (a b : ProfileDHighOwnFiveSupportC5CNF.TotalVertex) (q : ThreeColor) : Sat.Clause :=
  [.pos (OutsideDegreeCapCNF.outsideIncidentEdgeAtom a b (decodedNormalHostColor q))]
def units (i : Fin 72) : Sat.Fmla :=
  ((List.finRange 15).map fun p => (show Sat.Clause from [supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom selectedVertex (physicalBlockZeroVertex p) (3 : Fin 4))
      ((smallMask (smallCatalogueSupportIndex (smallRepresentativeRawIndex (pair i).2))).testBit p.val)])) ++
  ((List.finRange 15).map fun p => (show Sat.Clause from [supportLiteral
      (OutsideDegreeCapCNF.outsideIncidentEdgeAtom selectedVertex (physicalBlockOneVertex p) (3 : Fin 4))
      ((largeMask (largeCatalogueSupportIndex (largeRepresentativeRawIndex (pair i).1))).testBit p.val)])) ++
  ((List.finRange 5).flatMap fun a => (List.finRange 5).map fun b =>
    edge (freeVertex a) (physicalBlockOneVertex (largePhysical (pair i).1 b))
      (k15Template true (quotientFreeLabel i a) (quotientLargeLabel i b))) ++
  ((List.finRange 5).flatMap fun a => (List.finRange 4).map fun b =>
    edge (freeVertex a) (physicalBlockZeroVertex (smallPhysical (pair i).2 b))
      (k15Template true (quotientFreeLabel i a) (quotientSmallLabel i b))) ++
  ((List.finRange 5).flatMap fun a => (List.finRange 4).map fun b =>
    edge (physicalBlockOneVertex (largePhysical (pair i).1 a))
      (physicalBlockZeroVertex (smallPhysical (pair i).2 b))
      (k15Template true (quotientLargeLabel i a) (quotientSmallLabel i b)))

def physicalModel (i : Fin 72) : Sat.Fmla :=
  (quotientSmallSupportClauses i ++ quotientLargeSupportClauses i ++
   quotientFreeLargeClauses i ++ quotientFreeSmallClauses i ++
   quotientLargeSmallClauses i).map fun cl => cl.tail

theorem units_eq (i : Fin 72) : units i=physicalModel i := by
  simp [units,physicalModel,quotientSmallSupportClauses,quotientLargeSupportClauses,
    quotientFreeLargeClauses,quotientFreeSmallClauses,quotientLargeSmallClauses,
    pair_eq,smallMask_eq,largeMask_eq,largePhysical_eq,smallPhysical_eq,
    quotientLargeSupport,quotientSmallSupport,quotientLargeCatalogueIndex,quotientSmallCatalogueIndex,indexedLargeSupport,indexedSmallSupport,
    supportOfMask,edge,quotientGuardedEdgeClause,quotientLargePhysical,quotientSmallPhysical,Function.comp_def,List.append_assoc,List.map_flatMap,List.map_map]

#print axioms units_eq
end PricingG.D9Root12Fast
