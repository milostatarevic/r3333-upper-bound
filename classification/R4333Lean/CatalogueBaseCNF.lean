import R4333Lean.CatalogueBaseLiteral

/-!
# Small authoritative CNFs for the K15/K16 catalogue lemmas

These formulas deliberately contain no threshold circuits and no opaque
auxiliary-variable convention.  They are just the canonical good-colouring
CNF from `FiniteColorCNF`, followed by explicit unit clauses implementing
the elementary symmetry normalizations.
-/

namespace R4333

namespace CatalogueBaseCNF

open FiniteColorCNF

def interval (start length : Nat) : List Nat :=
  (List.range length).map (start + ·)

def setEdge (a b q : Nat) : Sat.Fmla :=
  [[Sat.Literal.pos (edgeAtom a b q)]]

def forbidEdge (a b q : Nat) : Sat.Fmla :=
  [[Sat.Literal.neg (edgeAtom a b q)]]

def setRootBlock (root start length color : Nat) : Sat.Fmla :=
  (interval start length).map fun v =>
    [Sat.Literal.pos (edgeAtom root v color)]

/-- Set the first `selected` vertices of a consecutive block to `color` and
forbid that colour on the remainder. -/
def selectRootPrefix
    (root start length selected color : Nat) : Sat.Fmla :=
  (List.range length).map fun position =>
    [if position < selected then
       Sat.Literal.pos (edgeAtom root (start + position) color)
     else Sat.Literal.neg (edgeAtom root (start + position) color)]

/-- Colour the first `selected` vertices of a block with `firstColor` and
the rest with `secondColor`. -/
def colorRootPrefix (root start length selected firstColor secondColor : Nat) :
    Sat.Fmla :=
  (List.range length).map fun position =>
    [Sat.Literal.pos (edgeAtom root (start + position)
      (if position < selected then firstColor else secondColor))]

/-- One of the sixteen normalized counterexample cubes for the assertion
that a non-red pair in a good `K16` has two common red neighbours. -/
def k16BadCommonLeaf (common redInBlueBlock : Nat) : Sat.Fmla :=
  k16BaseLiteral ++
  setEdge 0 1 1 ++
  setRootBlock 0 2 5 0 ++
  setRootBlock 0 7 4 1 ++
  setRootBlock 0 11 5 2 ++
  selectRootPrefix 1 2 5 common 0 ++
  selectRootPrefix 1 7 4 redInBlueBlock 0 ++
  selectRootPrefix 1 11 5 (5 - common - redInBlueBlock) 0

/-- Refinement of the sole large K16 LRAT leaf.  For `(common,split)=(3,2)`
the non-red residual blocks have sizes `2,2,5`; vertex 1 uses blue on four
of them because edge `01` is its fifth blue edge. -/
def k16BadCommonHardRefined (blueFirst blueSecond : Nat) : Sat.Fmla :=
  k16BadCommonLeaf 3 2 ++
  colorRootPrefix 1 5 2 blueFirst 1 2 ++
  colorRootPrefix 1 9 2 blueSecond 1 2 ++
  colorRootPrefix 1 11 5 (4 - blueFirst - blueSecond) 1 2

/-- One of four normalized counterexample cubes for the deficient-edge
extension rule at `K15`.  Unlike the earlier discovery certificate, no
secondary blue/green split and no threshold circuit is required. -/
def k15BadDeficientLeaf (redInBlueBlock : Nat) : Sat.Fmla :=
  k15BaseLiteral ++
  setRootBlock 0 1 4 0 ++
  setRootBlock 0 5 5 1 ++
  setRootBlock 0 10 5 2 ++
  ((interval 2 3).map (fun v =>
    [Sat.Literal.neg (edgeAtom 1 v 0)]) : Sat.Fmla) ++
  selectRootPrefix 1 5 5 redInBlueBlock 0 ++
  selectRootPrefix 1 10 5 (3 - redInBlueBlock) 0

/-- Refine a K15 deficient-edge leaf by sorting the two remaining colours
inside the three residual root-0 blocks.  The third blue count is forced by
the degree-five theorem. -/
def k15BadDeficientRefined
    (redInBlueBlock blueFirst blueSecond : Nat) : Sat.Fmla :=
  k15BadDeficientLeaf redInBlueBlock ++
  colorRootPrefix 1 2 3 blueFirst 1 2 ++
  colorRootPrefix 1 (5 + redInBlueBlock) (5 - redInBlueBlock)
    blueSecond 1 2 ++
  colorRootPrefix 1 (13 - redInBlueBlock) (2 + redInBlueBlock)
    (5 - blueFirst - blueSecond) 1 2

end CatalogueBaseCNF

end R4333
