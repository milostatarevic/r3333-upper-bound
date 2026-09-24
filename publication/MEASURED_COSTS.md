# Measured search costs

The proof uses 56,374 A/B/D formulas and 456 full-host C formulas. The table
reports the original successful search time summed over solver processes. It
excludes input generation, validation, independent reruns, unsuccessful attempts
and exploratory research. The complete C accounting and the separate A/B/D
second-solver cost appear below.

| Family | Formulas | Successful solver hours |
|---|---:|---:|
| A | 360 | 0.8378 |
| B | 5,096 | 21.3611 |
| D/UUU | 679 | 1.96 |
| D/UUT | 679 | 1.7294 |
| D/UTU | 6,576 | 18.9045 |
| D/UTT | 6,576 | 18.9200 |
| D/TTU | 18,204 | 61.8776 |
| D/TTT | 18,204 | 62.0167 |
| C | 456 | 1.5417 |

Profile and U/T definitions are given in [the proof](../proof.md). Different
families use different exhaustive decompositions, so a case count alone does
not measure difficulty. The C formulas use selector inequalities established
by the A/B/D computations; they do not independently replace those computations.

The mixed-D evidence combines two controller settings: the initial campaign
used per-case ceilings of 600 CPU seconds and 720 elapsed seconds; its
continuation removed those time ceilings. The table counts only accepted
UNSAT attempts, from either setting. Capped or interrupted attempts are
retained in the evidence and are excluded from these successful-search totals.

## Two-solver C verification

Every C formula has matching UNSAT answers from Kissat and CaDiCaL on the same
input hash. All attempts, including capped attempts that returned UNKNOWN,
contribute to the following totals.

| Phase | Solver CPU seconds | CPU hours |
|---|---:|---:|
| Kissat | 5,550.242931 | 1.5417 |
| CaDiCaL | 4,544.485844 | 1.2624 |
| CaDiCaL default continuations for 13 cases | 4,077.199416 | 1.1326 |
| CaDiCaL seed-varied continuations for 4 cases | 2,664.835519 | 0.7402 |
| **All C attempts** | **16,836.763710** | **4.6769** |

An UNKNOWN record is not a refutation. The complete input/result reconciliation
identifies the accepted UNSAT answer for each formula and solver. Generation,
audit and controller costs are recorded separately in
`evidence/final_validation/FINAL_COSTS_002.json` and the accompanying CPU ledger.
All archive paths are relative to the extraction described in the
[reproduction guide](REPRODUCIBILITY.md).

## Complete A/B/D second-solver verification

CaDiCaL 3.0.1 reran all **56,374 original A/B/D formulas** and returned an
accepted UNSAT result for every case, with **zero SAT, UNKNOWN or error results**.
The [acceptance receipt](checks/ABD_SECOND_SOLVER.json) records the exact
input and result accounting.

| Measure | Recorded value |
|---|---:|
| Native solver CPU seconds | 888,530.997869 |
| Native solver CPU hours | 246.814166 |
| Launch (UTC) | 2026-09-22 18:31:14 |
| Last solver finish (UTC) | 2026-09-24 07:49:45 |
| Elapsed duration, rounded to the nearest second | 37h18m30s |

CPU time is summed across native solver processes. Elapsed time measures the
interval from launch to the last solver finish, with up to eight solvers
running in parallel. This verification cost is additional to the original
successful-search table and separate from the C reruns, input checks and
Lean build.
