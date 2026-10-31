# Measured computational costs

Every one of the 296,797 formulas has an UNSAT result from Kissat 4.0.4,
with default search options. A five-minute first pass was followed by longer
retries where needed. The table sums native process CPU time for all 296,952
recorded attempts, including 132 timeouts and 23 interruptions; all unresolved
cases were subsequently refuted. It excludes input generation, evidence
checking, Lean compilation and exploratory research.

| Family | Formulas | Kissat CPU hours |
| --- | ---: | ---: |
| A | 360 | 0.27 |
| B | 5,096 | 6.45 |
| D / UUU | 679 | 1.63 |
| D / UUT | 679 | 1.68 |
| D / UTU | 6,576 | 17.60 |
| D / UTT | 6,576 | 18.12 |
| D / TTU | 18,204 | 59.82 |
| D / TTT | 18,204 | 60.36 |
| E / UUU | 2,037 | 4.77 |
| E / UUT | 6,111 | 14.51 |
| E / UTT | 59,184 | 155.84 |
| E / TTT | 163,836 | 526.91 |
| C1, marked entrance | 692 | 0.46 |
| C2, marked entrance | 7,840 | 12.51 |
| All-five guards | 3 | 0.03 |
| Mixed marked balance | 720 | 5.79 |
| **Total** | **296,797** | **886.75** |

The profile and template names are defined in [the proof](../proof.md).
The case counts measure the exhaustive boundary; they are not estimates
of relative difficulty. Rounded table entries need not sum exactly.

## Elapsed time and concurrency

E execution spanned **59.33 hours**, A/B/D **15.82 hours**, and the direct
entrance/balance campaign **1.61 hours**, each with up to 12 solver workers.
These are measured execution intervals, not predictions for a dedicated
machine. Other work shared the host, and elapsed intervals include pauses
and sleep.

CPU time is summed over native processes. Elapsed time includes scheduling
and input preparation between those processes and cannot be obtained by
adding their CPU times.

## Mathematical checking and storage

The complete 1,390-module Lean build and all four exact-input comparisons
passed. Their receipts are identified in the [release index](checks/K60_RELEASE.json).
Those costs are separate from native SAT solving.

The native archive retains the complete per-attempt logs and elapsed durations.
CPU totals above sum the Kissat `process time` field from each log, for exactly
the histories authenticated by its manifest
`089599c2c4ed17524bb73727584391f16f85272facaf283d3923e4938f770d95`.
The total before rounding is **3,192,285.00 CPU-seconds**.
Independent CaDiCaL verification is running and is not included in these totals.
