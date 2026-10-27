# Verification method

We give a computer-assisted proof of R(3,3,3,3) ≤ 61. Its mathematical reduction is formalized in Lean. The exhaustive native SAT exclusions are confirmed by two solvers, with exact input identities linking those searches to the formal formulas.

## The proof boundary

[`UniformK61.WholeProof.ramsey61`](../formal/src/UniformK61/WholeProof.lean) takes the single premise `AllNativeUnsat`: all **56,723 concrete formulas** in its finite case type are unsatisfiable. Classification completeness, case coverage, physical transport and encoding soundness are proved within the development. Any good coloring of K61 supplies a satisfying assignment to at least one of those formulas.

The case type consists of 56,374 A/B/D formulas, 346 direct C entrance formulas and three globally balanced formulas. Every formula contains the same full K61 physical base. The marked cases add signed physical facts. Their normalized support-and-word configurations cover every actual supplied mark, and a finite whole-host transport check connects each configuration to a retained case. The balanced cases also encode support choices and the visible parts of actual critical neighborhoods, with proved auxiliary witnesses.

The verification boundary has three parts:

- **The mathematical statement and Lean kernel.** The definitions describe the physical coloring problem. Lean checks the reductions, finite mathematical covers and satisfiability implications.
- **Formula binding and result accounting.** External tools compare complete Lean-emitted formulas with the native input catalogue, then join their hashes to the required case census and recorded solver inputs and results.
- **Native UNSAT answers.** Each solver's answer excludes its exact input formula. The large K61 refutations are not kernel-checked certificates.

Kissat 4.0.4 and CaDiCaL 3.0.1 agree on every required formula, giving 113,446 UNSAT results. Both run with default options and no CPU or wall-time limit. The complete accounting has no SAT, UNKNOWN, error or missing result. Two-solver agreement corroborates the computation; it does not remove the explicit computational premise from the Lean theorem.

Hashes establish file identity. A theorem's standard-axiom audit does not prove the external byte comparisons or a native solver answer. The [reproduction guide](REPRODUCIBILITY.md), [Lean build guide](../formal/BUILD.md) and [binding guide](../formal/reproduce/uniform/README.md) give the distinct checks.

## Classification certificates and mathematical coverage

The K15/K16 classification has its own local completeness proofs and **55 small CNF/LRAT pairs** checked by Lean. These establish that every relevant critical neighborhood is represented by the literal templates. They are separate from the native K61 case exclusions. [Classification provenance](CLASSIFICATION_PROVENANCE.md) identifies their sources and checking method.

The [source manifest](../formal/SOURCE_MANIFEST.json) fixes the complete mathematical source closure. The [formalization scope](FORMALIZATION_STATUS.md) states the exact endpoint and how the physical covers and auxiliary witnesses are supplied. All actual vertices and overlapping neighborhoods refer to one coloring, with one global color palette.

The [release checks](RELEASE_CHECKS.md) distinguish the complete source build, final theorem audit, full input binding and native result reconciliation. The compact CI target checks source/data integrity and physical-base foundations; it is not a substitute for those complete checks.

## Relation to the earlier bound

Fettes, Kramer and Radziszowski combine mathematical reductions and exhaustive computations in their [2004 paper, §§5–6](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf). Their use of independently compared computations is a relevant precedent for an explicit computational proof.

Here the mathematical reduction is also checked in Lean, while the main computational exclusions remain native SAT results. The repository states these mechanisms directly rather than treating different forms of verification as interchangeable.

## Costs and responsibility

The [cost table](MEASURED_COSTS.md) gives the measured search workload and its accounting scope. The author takes responsibility for the mathematical account, evidence and corrections. The work was developed with extensive AI assistance and has not yet undergone independent human review; [attribution](ATTRIBUTION.md) records that context.
