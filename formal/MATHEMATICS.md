# Mathematical dependency map

The endpoint is [`UniformK61.WholeProof.ramsey61`](src/UniformK61/WholeProof.lean). Its only external premise is unsatisfiability of the concrete formulas indexed by `WholeProof.Case`:

```lean
def AllNativeUnsat : Prop :=
  ∀ k : Case, ¬∃ w : Valuation, FormulaSat w (formula k)
```

All vertices and edge colors in the reductions belong to one actual K61 coloring. Template coordinates and palette maps describe that coloring; they do not introduce independent colorings on overlapping neighborhoods.

[`CNF`](src/UniformK61/CNF.lean) supplies the clause and valuation semantics. [`Physical`](src/UniformK61/Physical.lean) defines the shared edge variables, one-color clauses and triangle prohibitions; [`Core`](src/UniformK61/Core.lean) adds signed physical facts. [`PhysicalHelpers`](src/UniformK61/PhysicalHelpers.lean) supplies the elementary palette and edge-index facts used by the support transports. [`HostNormalization`](src/UniformK61/HostNormalization.lean) supplies whole-host vertex and palette maps.

## Marked A/B/D and C covers

A normalized configuration consists of fixed root-cell sizes and template types, selected foreign supports, a free support in reference order, and one of the 600 cross-support words. Its recorded facts include every root spoke, each supplied template, the free-support pattern, the word and exact marked-neighborhood membership.

The finite coverage criterion supplies a retained case and one whole-host vertex and palette transformation for every normalized configuration. Every target fact must pull back to a recorded source fact. [`UnitTransport.covers_satisfiable`](src/UniformK61/UnitTransport.lean) expresses this physical implication. The support and word checks, including their whole-template actions and all signed membership facts, establish the criterion for the complete retained lists.

The A/B/D construction is implemented by [`CommonCover`](src/UniformK61/CommonCover.lean), [`UUPhysicalCover`](src/UniformK61/UUPhysicalCover.lean) and [`UUFiniteCover`](src/UniformK61/UUFiniteCover.lean). [`CommonHost`](src/UniformK61/CommonHost.lean) extends the coordinates to all 61 vertices; [`CommonSoundness`](src/UniformK61/CommonSoundness.lean) proves the corresponding physical facts. The retained units are defined in [`CommonFormula`](src/UniformK61/CommonFormula.lean) and [`MarkedUU`](src/UniformK61/MarkedUU.lean). [`CommonCases`](src/CompletionC/CommonCases.lean) defines the admitted case indices; [`SupportEdges`](src/CompletionC/SupportEdges.lean) gives their physical support-edge coordinates. Together these covers contain 360 A, 5,096 B and 50,918 D cases.

[`ABDProof.selector`](src/UniformK61/ABDProof.lean) applies these exclusions to obtain the three strict incoming-ticket bounds for A, B and D. These bounds are conclusions of the case covers, not additional assumptions.

[`CEntrance.physical_cover`](src/UniformK61/CEntranceCover.lean) proves the generic normalized-entrance cover, and [`CEntrance.actual_C_cover`](src/UniformK61/CEntranceFinal.lean) supplies the final witness interface for the direct 346-case catalogue. Its physical layout contains two classified 16-neighborhoods, the actual marked neighborhood, and the complete remaining cells. It requires no critical template for a 14-vertex cell and does not assume that such a cell extends to a critical coloring.

All these formulas are the shared good-coloring base followed by signed physical edge units. Their satisfying valuations are constructed directly from the transported full host.

## The globally balanced case

If there is no C entrance, double counting of tickets and the A/B/D bounds yield [`SynchronizedCE`](src/Ramsey61/Selector.lean). The four [`BalancedStructure`](src/UniformK61/BalancedStructurePair.lean) modules derive one common high-color pair by elementary counting:

1. In a good three-colored K15 or K16, each color degree is between n−11 and 5. A color-closed component has at least twice its minimum degree, so each internal color graph is connected.
2. Reciprocity therefore makes every high-color flag constant within an actual critical neighborhood. The parity obstruction supplies a C root; an E vertex would force a 15-neighborhood into two intersections of size at most five.
3. High-color pairs agree across critical edges. Any two 32-element critical-neighbor sets intersect in the 61-vertex host, so the pair is common to every vertex.

[`UniformK61.BalancedHost.uniform_to_three_owners`](src/UniformK61/BalancedHostOwners.lean) normalizes one root, one global palette, and its two actual 16-neighborhoods. Exchanging those two cells together with their high colors leaves the three template pairs UU, UT and TT. The named degree vector at every vertex is (16,16,14,14).

[`BalancedVisible`](src/UniformK61/BalancedVisible.lean) proves that each observed part of an opposite high-color neighborhood embeds into a classified K16 template. All physical edges between observed vertices are preserved. The two-color intersection bound also supplies the five-element cross supports.

The finite anchor catalogue covers all 320 ordered five-anchor embeddings with the fixed reference coloring into the two literal templates. Its whole-template maps give six coordinate states. [`BalancedAnchorSupportFinite`](src/UniformK61/BalancedAnchorSupportFinite.lean) covers every independent five-subset. [`BalancedEncodingActualLocal`](src/UniformK61/BalancedEncodingActualLocal.lean) transports the actual observed embeddings into those coordinates, preserving all anchor and member-pair colors. Inactive vertices receive no role; active vertices receive distinct roles.

[`BalancedEncodingValuation`](src/UniformK61/BalancedEncodingValuation.lean) combines the support and local-embedding witnesses in disjoint variable ranges, without changing any physical edge value. [`BalancedEncoding.actual_uniform_cover`](src/UniformK61/BalancedEncodingActual.lean) consequently supplies a satisfying valuation of one of the three complete balanced formulas from any good globally balanced host. It has no extra finite-coverage or auxiliary-witness premise.

## Classification and final composition

[`ClassificationAdapter`](src/Ramsey61/ClassificationAdapter.lean) connects the complete K15/K16 classification to actual neighborhoods and their palette maps. Its 55 included CNF/LRAT pairs are checked by the Lean build. The classification is used wherever a critical neighborhood is replaced by a literal template.

`WholeProof.ramsey61` splits on the existence of an actual C entrance. That branch reaches one of the 346 C formulas. The other branch derives the common high pair and reaches one of the three balanced formulas. Together with the 56,374 A/B/D exclusions, this gives the exact 56,723-case computational premise.

The [input-binding checks](reproduce/uniform/README.md) separately compare the complete Lean-emitted formulas with the native input catalogue. Native solver UNSAT remains external; the mathematical connection to those exact formulas is proved in Lean.
