# A/B/D formula and finite-data index

[Section 3 of the proof](../proof.md#3-excluding-high-h-roots-of-profiles-a-b-and-d)
uses **56,374 exact A/B/D formulas**. This index connects the mathematical
case tables to the finite data, input manifests and reconstruction assets.
The [machine-readable index](ABD_EVIDENCE_INDEX.json) gives exact byte sizes
and SHA256 hashes for all 85 indexed snapshot files, including every shared
prefix and the UUU/UUT sparse bases and dense maps.

Paths beginning `evidence/` or `support/` below are relative to the
authenticated extracted `archives/evidence-v1.tar.gz` snapshot. They are
archive locators, not links to files in a clean checkout. Follow the
[extraction instructions](REPRODUCIBILITY.md) first. The archive SHA256 is
`2b85cac94df0317a532aa823cfea93ac83738093fc854805896943f90d468757`.

## Exact formula manifests

| Family | Formulas | Snapshot locator |
| --- | ---: | --- |
| A | 360 | `evidence/A/full_inputs_000/MANIFEST.json` |
| B | 5,096 | `evidence/B/full_inputs_000/MANIFEST.json` |
| D/UUU | 679 | `evidence/D/UUT/full_inputs_000/MANIFEST.json` |
| D/UUT | 679 | `evidence/D/UUT/full_inputs_000/MANIFEST.json` |
| D/UTU | 6,576 | `evidence/D/mixed/full_inputs_UTU_000/MANIFEST.json` |
| D/UTT | 6,576 | `evidence/D/mixed/full_inputs_UTT_000/MANIFEST.json` |
| D/TTU | 18,204 | `evidence/D/mixed/full_inputs_TTU_000/MANIFEST.json` |
| D/TTT | 18,204 | `evidence/D/mixed/full_inputs_TTT_000/MANIFEST.json` |

These are the seven manifests pinned by
[`reproduce/abd_inputs.py`](../reproduce/abd_inputs.py). A/B and mixed-D
manifests contain case IDs, physical unit suffixes, prefix identities and
complete formula hashes. Their shared prefixes are stored in each manifest's
directory, under `prefixes/` for A/B. The machine index lists every exact path.

The shared UUT manifest records two different formula families. Its
`old_virtual_dense_sha256` and `historical_control` fields bind each UUU case
to the original UUU base and its own native result. Its `cnf_sha256` fields
bind the separately searched UUT formulas. The reconstructor chooses the
appropriate sparse base, applies the pinned bijective dense map and appends
the case units. UUT solver answers are not used for UUU. The UUU result
locator is `evidence/D/UUU/results/<case_id>/RESULT.json`.

## Finite supports and matrix representatives

| Scope | Snapshot locator |
| --- | --- |
| A physical case census | `evidence/A/SELECTED_A_VERIFIED_CENSUS_000.json` |
| B physical case census | `evidence/B/SELECTED_B_VERIFIED_CENSUS_000.json` |
| Mixed-D ordered support/matrix census | `evidence/D/mixed/MIXED_D_VERIFIED_CENSUS_000.json` |
| Common matrix representative tables | `support/workspace/r4333_upper/pro_findings_review_2026_09_11/ramsey61_research/direct_profile_counts.json` |
| Rooted matrix construction | `support/workspace/r4333_upper/pro_findings_review_2026_09_11/ramsey61_research/marked_catalogue.py` |
| Profile and template definitions | `direct_profiles.py` and `template_math.py` in that same directory |

The three verified censuses expose the data through these fields:

- `finite_evidence.supports` gives physical support orders and the
  whole-block actions inducing the allowed support permutations.
- `finite_evidence.catalogues` records all four ordered shapes, their
  600-word catalogues and sorted-word hashes.
- `groups.<foreign_kind>.stages.<stage>.cases[].reps` contains the stored
  representative color words, encoded as hexadecimal bytes.
- Stages `0`, `1`, `2`, and `None` mean support sizes 455, 545, 554, and 555.
  The corresponding cross-edge words have 65, 65, 65, and 75 color entries,
  ordered by group pairs `(0,1)`, `(0,2)`, `(1,2)`, then the canonical vertex
  indices within each pair.

The mixed-D census retains both ordered deficiency orientations. The TT
input manifests select the cover from those data by ordering the two
five-support orbit indices and retaining every matrix representative on a
diagonal pair. The mathematical justification and the meaning of the D
constraints are given in [D cover and encoding](D_COVER_AND_ENCODING.md).

The recorded checker outputs are `finite_check_output_000/CHECK_OUTPUT.json`
under `evidence/A/`, `evidence/B/`, and `evidence/D/mixed/`. The machine index
also identifies the three independent finite-checker sources. These records
check finite supports, actions and representative coverage; formula identity
and native refutation are separate evidence.

## The six U/U component censuses

These six files are under `evidence/D/UUU/census/` and describe the 679 labels
used for each of D/UUU and D/UUT:

| File | Labels |
| --- | ---: |
| `P15_MATRIX_ONLY_189.json` | 189 |
| `D9_STRONG_ROOT2.json` | 72 |
| `D9_TWISTED_ROOT1.json` | 132 |
| `D9_TWISTED_ROOT4.json` | 132 |
| `D9_TWISTED_ROOT12.json` | 72 |
| `D10_B2P15_82.json` | 82 |

The assignment covers and exchange relation behind these component labels
are also indexed:

| Role | Snapshot locator |
| --- | --- |
| P15's 372-to-189 exchange relation | `support/workspace/r4333_upper/profile_d_four_support_discovery/uuu_b2_p15_swap_quotient.json` |
| D9 assignment construction | `support/r3333-fable/continuation/locks/duuu/discovery/d9_case_census.py` |
| D9 finite permutation order | `support/workspace/r4333_upper/profile_d_degree9_discovery/strong_case_b2_p15_quotient/lean-permutations.tsv` |
| D9 U/root2 assignment orbits | `support/workspace/r4333_upper/profile_d_degree9_discovery/strong_case_b2_p15_quotient/assignment-orbits.json` |
| D9 T/root1 assignment orbits | `support/r3333-fable/continuation/locks/duuu/discovery/twisted_root1_orbits.json` |
| D9 T/root4 assignment orbits | `support/r3333-fable/continuation/locks/duuu/discovery/twisted_root4_orbits.json` |
| D9 T/root12 assignment orbits | `support/r3333-fable/continuation/locks/duuu/discovery/twisted_root12_orbits.json` |

These records describe the finite assignment quotient. The six component
censuses bind its retained labels to formula suffixes; the two roles must
be checked together. Historical source paths in the assignment program are
provenance references, not portable execution instructions.

The D10 matrix data are present at
`support/r3333-fable/continuation/inputs/r4333-profile-d-degree10-discovery-uuu-b2-p15.json`.
The corresponding literal data source is
`support/workspace/R4333Lean/ProfileDDegreeTenMatrixLeafDataUUU2P15.lean`.
Both are pinned in the machine index and expose the literal matrix arrays.
The [formal dependency map](../formal/MATHEMATICS.md) identifies the complete
Lean owner, support, matrix, transport and encoding arguments that consume
these data.

## Verification scope

The [complete reconstruction receipt](checks/ABD_ALL_INPUTS_001.json) records
agreement with all 56,374 formula hashes. The
[materialization receipt](checks/ABD_MATERIALIZATION_001.json) covers 56
representatives spanning every distinct prefix/family, and the
[reconstructor](../reproduce/abd_inputs.py) checks its specified input-byte
identities. Reconstruction commands are in
[REPRODUCIBILITY.md](REPRODUCIBILITY.md). The separate
[native-result checker](../reproduce/abd_native.py) joins all 56,374
reconstructed formulas to their authenticated UNSAT records and logs, including
mixed-D predecessor adoptions and the UUT pilot. It checks recorded evidence
without rerunning a solver.

All 85 indexed files were rehashed and matched to the authenticated archive
manifest records, and the seven input manifests' case counts were checked.
That index check performs no finite mathematical search, solver execution,
certificate replay or Lean build. The proof uses the recorded native Kissat
answers for A/B/D; these formulas have no checked refutation certificates or
complete second-solver replay. The [dependency ledger](DEPENDENCIES.json)
links the corresponding native acceptance records. The
[Lean theorem](../formal/src/PricingIntegration/NativeWholeProof.lean) proves the
complete mathematical reduction under `AllNativeUnsat`; the
[formula-binding tools](../formal/reproduce/README.md) compare all 55,016
common A/B/mixed-D and 1,358 original UUU/UUT formulas with retained or
reconstructed input bytes, whose hashes match the runner-recorded native inputs. The [formalization status](FORMALIZATION_STATUS.md) separates
that proved reduction from the external byte checks and native UNSAT evidence.
