# Measured computational costs

Every one of the 56,723 formulas has an UNSAT result from Kissat 4.0.4
and CaDiCaL 3.0.1, both with default search options and no CPU or
elapsed-time limit. The table sums native process CPU time for exactly
the 113,446 required executions. It excludes input generation, evidence
checking, Lean compilation and exploratory research.

| Family | Formulas | Kissat CPU hours | CaDiCaL CPU hours | Combined CPU hours |
| --- | ---: | ---: | ---: | ---: |
| A | 360 | 0.31 | 1.71 | 2.02 |
| B | 5,096 | 7.45 | 41.21 | 48.66 |
| D / TTT | 18,204 | 66.15 | 184.43 | 250.59 |
| D / TTU | 18,204 | 65.23 | 168.26 | 233.49 |
| D / UTT | 6,576 | 20.67 | 45.89 | 66.56 |
| D / UTU | 6,576 | 20.04 | 40.03 | 60.07 |
| D / UUT | 679 | 2.01 | 6.47 | 8.47 |
| D / UUU | 679 | 1.92 | 3.25 | 5.18 |
| C, marked entrance | 346 | 0.26 | 1.42 | 1.67 |
| C, perfect balance | 3 | 0.02 | 0.03 | 0.05 |
| **Total** | **56,723** | **184.06** | **492.71** | **676.77** |

The profile and template names are defined in [the proof](../proof.md).
The case counts measure the exhaustive boundary; they are not estimates
of relative difficulty. Rounded table entries need not sum exactly.

## Elapsed time and concurrency

A/B/D execution spanned **59.83 hours** with up to 12 solver
workers. The 346 C entrances spanned **42 minutes**, with up to
12 workers. The three balanced cases spanned **38 seconds**,
with up to 6 workers. These are measured execution
intervals, not predictions for a dedicated machine. Other work shared the
host, and the C interval includes a single long-running tail.

CPU time is summed over native processes. Elapsed time includes scheduling
and input preparation between those processes and cannot be obtained by
adding their CPU times. The host had 16 logical CPUs and 128 GiB RAM.

## Perfect balance

The balanced cases use 13,656 variables and 524,462 clauses each. Their
individual native costs, rounded to seconds, are:

| Case | Kissat CPU seconds | CaDiCaL CPU seconds |
| --- | ---: | ---: |
| UU | 30 | 32 |
| UT | 29 | 37 |
| TT | 19 | 32 |

The six executions together used **179 CPU-seconds**. Their results
have the same uncapped policy and exact-input checks as every other case.

## Mathematical checking and storage

The [formal measurements](../formal/MEASUREMENTS.md) report the complete
Lean build, the executed formula-binding checks, memory and disk usage.
Those costs are separate from native SAT solving. The evidence retains
raw per-execution measurements, input hashes and logs, indexed by the
[release checks](RELEASE_CHECKS.md).
