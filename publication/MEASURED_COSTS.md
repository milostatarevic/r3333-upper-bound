# Measured computational costs

Every one of the 296,081 selected formulas has an accepted UNSAT result from
Kissat 4.0.4 and CaDiCaL 3.0.1, using default search options. The table reports
**successful-run CPU time**: the complete accepted UNSAT execution of each
formula is counted exactly once per solver. Earlier timed-out or interrupted
attempts are excluded from these headline values and retained separately below.
Input generation, evidence checking, Lean compilation, exploratory research,
sleep and wall-clock elapsed time are not solver CPU time.

| Family | Formulas | Kissat CPU hours | CaDiCaL CPU hours |
| --- | ---: | ---: | ---: |
| A | 360 | 0.27 | 1.88 |
| B | 5,096 | 6.45 | 37.56 |
| D/UUU | 679 | 1.63 | 2.65 |
| D/UUT | 679 | 1.68 | 5.53 |
| D/UTU | 6,576 | 17.60 | 36.12 |
| D/UTT | 6,576 | 18.03 | 40.67 |
| D/TTU | 18,204 | 59.09 | 155.32 |
| D/TTT | 18,204 | 59.95 | 159.63 |
| E/UUU | 2,037 | 4.77 | 6.29 |
| E/UUT | 6,111 | 14.51 | 22.56 |
| E/UTT | 59,184 | 154.69 | 211.06 |
| E/TTT | 163,836 | 518.39 | 767.98 |
| C1 entrance | 692 | 0.46 | 1.32 |
| C2 entrance | 7,840 | 12.51 | 85.34 |
| All-five formulas | 3 | 0.03 | 0.03 |
| C2 compatibility | 4 | 1.48 | 1.60 |
| **Total** | **296,081** | **871.53** | **1535.55** |

The profile and template names are defined in [the proof](../proof.md).
These are exhaustive formula counts, not estimates of relative difficulty.
The [machine-readable timing report](checks/SUCCESSFUL_RUN_TIMINGS.json) binds
every successful execution to the selected exact-input census and complete
native capsule. The independent publication check recomputes the totals from
full logs. Seconds are summed before rounding to hours; rounded rows need not
sum exactly. The four direct C2 runs are included once per solver.

## Attempt accounting

The immutable native records retain all attempts. A timeout or interruption
never counts as a refutation. For the selected publication boundary:

| Measurement | Kissat | CaDiCaL |
| --- | ---: | ---: |
| Successful runs | 296,081 | 296,081 |
| Earlier unsuccessful attempts | 155 | 1,097 |
| All recorded attempts | 296,236 | 297,178 |
| Successful-run CPU seconds | 3,137,504.980409 | 5,527,990.401676 |
| Unsuccessful-attempt CPU seconds | 39,265.54 | 409,372.65 |
| All-attempt CPU seconds | 3,176,770.520409 | 5,937,363.051676 |
| All-attempt CPU hours | 882.44 | 1,649.27 |

Kissat's excluded attempts comprise 132 timeouts and 23 interruptions.
CaDiCaL's comprise 1,076 effective timeouts and 21 interruptions. One reviewed
native-alarm timeout remains recorded as raw ERROR/exit -14; its authenticated
log is adjudicated separately, and the original record is unchanged.
Successful plus unsuccessful CPU seconds equal the all-attempt total exactly.
The previous all-attempt metadata has not been relabelled as successful-only.

The original production boundary has 296,797 formulas. The selected package
replaces 720 old marked-balance formulas with four direct C2 compatibility
formulas, leaving 296,081. The omitted 720 runs were all UNSAT in each solver;
their CPU totals were 20,829.35 seconds for Kissat and 15,336.43 for CaDiCaL.
Thus original production CPU expenditure, excluding the separate direct C2
experiment, was 3,192,285.00 seconds for Kissat and 5,946,932.66 for CaDiCaL.
The [campaign accounting](checks/CAMPAIGN_CPU_ACCOUNTING.json) reconciles these
figures with the selected totals; they are not the paper's headline metric.

Production CPU values are the unique native process-time field in each full
log. The direct C2 experiment measures child user plus system CPU time, adding
5,314.870409 seconds for Kissat and 5,766.821676 for CaDiCaL. These measurements
and their original precision are retained in the evidence.

## Limits, elapsed time and concurrency

Each production campaign used at most 12 solver workers. Kissat's E campaign
used limits of 300, 1,800 and 7,200 seconds; its A/B/D and closure campaigns
also allowed 28,800 and 86,400 seconds. CaDiCaL used the fixed shuffled order
and the schedule 300/1,800/7,200/28,800/86,400 seconds, with the unchanged
cap-plus-five-second elapsed backstop. Its initial 300-second stage resolved
295,770 original production cases; the later stages resolved 981, 43 and 3
respectively. No 86,400-second attempt was needed. Interruptions and timeouts
remained unresolved until their subsequent accepted UNSAT result.

The original CaDiCaL campaign started at 2026-10-31 04:18:56.715684 UTC and
its final result finished at 2026-11-06 07:02:52.397037 UTC. Calendar elapsed
was **528,235.681353 seconds (6 days, 2 hours, 43 minutes, 56 seconds)**.
This interval includes input preparation, scheduling, sleep, the deliberate
C2 experiment pause and the diagnostic timeout-handling stop. It is not CPU
time, and resumed-session age is not substituted for whole-campaign duration.

The earlier Kissat E execution spanned **59.33 hours** and A/B/D **15.82 hours**,
each with up to 12 workers. The four direct C2 formulas were run in both
solvers over **35.25 minutes**, with eight workers. These are measured
execution intervals, not predictions for a dedicated machine. Other work
shared the host. CPU sums cannot be converted into elapsed time merely by
dividing by the maximum worker count.

## Mathematical checking and storage

The formal package contains 1,314 selected Lean modules. Its retained build
reuses 1,309 authenticated unchanged modules and recompiles the five changed
or dependent modules. The build and four complete exact-input comparisons
are separate from native SAT solving. Their receipts, both solver audits,
timing report, archive hashes and final source bindings are identified in the
[release index](checks/K60_RELEASE.json). A fully fresh rebuild is described
in the [reproduction guide](../REPRODUCIBILITY.md).
