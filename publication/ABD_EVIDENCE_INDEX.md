# A/B/D formula and finite-data index

[Section 4 of the proof](../proof.md#4-the-a-b-and-d-ticket-bounds)
uses **56,374 exact A/B/D formulas**. Every formula uses the shared
physical K61 base followed by signed physical unit facts. This index
connects the mathematical covers, finite data and exact native inputs.

## Current case boundary

| Family | Formulas |
|---|---:|
| A | 360 |
| B | 5,096 |
| D/UUU | 679 |
| D/UUT | 679 |
| D/UTU | 6,576 |
| D/UTT | 6,576 |
| D/TTU | 18,204 |
| D/TTT | 18,204 |
| **Total** | **56,374** |

The complete current input catalog additionally contains 346 C
entrance cases and three balance cases, totaling 56,723 formulas.
In the extracted current evidence package, `inputs/MANIFEST.json`
declares this boundary and `inputs/cases.jsonl.gz` records each case
identity, ordered units or balance input path, dimensions and full
formula hash. The manifest records the exact catalog identity.

The common physical base is `inputs/base.clauses`, with SHA256
`f974e4a1e44ae758ba748fc91838cd820cfb807ed4c09e7ffa5dc661d267565e`.
It has 7,320 variables and 156,770 clauses. A/B/D case formulas
add their physical units without introducing auxiliary variables.

[uniform_k61.py](../reproduce/uniform_k61.py) is the generator.
The [reproduction guide](REPRODUCIBILITY.md) gives extraction,
generation, verification and solver commands. Paths beginning
`inputs/`, `sources/` or `math/` here are relative to the extracted
current evidence package, not additional checkout files.

## Finite support and word data

The immutable finite-source archive is
[`archives/evidence-v1.tar.gz`](../archives/evidence-v1.tar.gz),
SHA256 `2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757`.
The following are locators inside its authenticated extracted tree:

| Finite-data role | Locator |
|---|---|
| A support and representative census | `evidence/A/SELECTED_A_VERIFIED_CENSUS_000.json` |
| B support and representative census | `evidence/B/SELECTED_B_VERIFIED_CENSUS_000.json` |
| Mixed-D support and representative census | `evidence/D/mixed/MIXED_D_VERIFIED_CENSUS_000.json` |
| A physical case records | `evidence/A/full_inputs_000/MANIFEST.json` |
| B physical case records | `evidence/B/full_inputs_000/MANIFEST.json` |
| Mixed-D physical case records | `evidence/D/mixed/full_inputs_KIND_000/MANIFEST.json`, with KIND equal to UTU, UTT, TTU or TTT |

These retained source records supply finite supports, reference
orders, cross words and physical facts. Their embedded input hashes
do not replace the current full-K61 catalog hashes above. Current
formula identity is checked after constructing the shared base and
the complete physical units.

In each finite census, `finite_evidence.supports` identifies the
support orders and whole-template actions. `finite_evidence.catalogues`
records the four support shapes and their 600-word lists. Representative
words occur in `groups.<foreign_kind>.stages.<stage>.cases[].reps`.
Stages 0,1,2,None correspond to shapes (4,5,5), (5,4,5), (5,5,4), (5,5,5).
Cross-word entries are ordered by support pairs (0,1), (0,2), (1,2), then their
reference coordinates; the lengths are 65,65,65,75.

The [machine-readable index](ABD_EVIDENCE_INDEX.json) gives exact
retained file identities and locators. The mathematical use of the
source data is proved in the Lean cover modules, rather than assumed
from a matching file hash or a case count.

## Normalized configurations and retained cases

For fixed root-cell sizes and template types, a normalized configuration
consists of a selected foreign support pair and one of the 600 words.
It records all root and supplied-template edges, the free-support pattern,
the word and complete signed marked-neighborhood membership.

Every retained family meets one finite coverage condition: for every
normalized configuration there is a target case and a whole-host vertex
and palette transformation such that each pulled-back target fact is a
recorded source fact. These transformations preserve the actual host,
including all negative membership facts. The condition is established
in the Lean covers and described in [the proof](../proof.md#33-finite-words-and-whole-cell-symmetries).

The normalized physical case table
[marked_uu.json](../reproduce/data/marked_uu.json) has schema
`UNIFORM_K61_MARKED_UU_DATA_1`. It indexes 679 records by the integers
0 through 678 and supplies their physical facts and exact native case
identifiers. The marked U or T template gives the D/UUU or D/UUT
formula. The Lean definition is
[MarkedUU.caseUnits](../formal/src/UniformK61/MarkedUU.lean), with
`Fin 679` as its index type. Case identifiers are opaque labels;
coverage follows from the finite transport proof.

The [D supplement](D_COVER_AND_ENCODING.md) describes the complete D
cover, its whole-host symmetries and physical formula semantics.

## Formula binding and native evidence

The Lean A/B/D case type contains 360 A, 5,096 B and 50,918 D cases. The
[uniform binding driver](../formal/reproduce/uniform/README.md)
emits all of them from the accepted mathematical build and
compares every ordered physical fact and complete formula identity
with the current input catalog. The full binding also includes
the 346 direct C cases and the three balance inputs.

The current evidence package preserves native records without
rewriting case IDs, commands or logs. Each current A/B/D formula
has its own Kissat 4.0.4 and CaDiCaL 3.0.1 UNSAT result, obtained
with default options and no CPU or elapsed-time cutoff. The
[release verifier](../reproduce/uniform_release.py) checks the
complete current case mapping and all 112,748 A/B/D outcomes,
together with the 698 C/balance outcomes and mathematical acceptance
records. Exact formula hashes, command and binary identities,
native exit codes and full solver output are all checked.

Coverage, input identity and native execution have different roles.
The [Lean theorem](../formal/src/UniformK61/WholeProof.lean) proves
the complete mathematical reduction under `AllNativeUnsat` for
the concrete formulas. The byte-binding checks connect those
definitions to native inputs. The large native refutations remain
external evidence under the
[stated proof standard](TRUST_AND_CERTIFICATION.md).
