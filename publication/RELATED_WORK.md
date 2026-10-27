# Related work and the scope of the claimed improvement

S. Fettes, R. L. Kramer and S. P. Radziszowski proved the upper bound 62 in *An Upper Bound of 62 on the Classical Ramsey Number R(3,3,3,3)*, Ars Combinatoria **72** (2004), 41–63. [Publisher's paper](https://combinatorialpress.com/article/ars/Volume%20072/volume-72-paper-5.pdf).

Radziszowski's *Small Ramsey Numbers*, revision 18 dated April 24, 2026, records 51 ≤ R(3,3,3,3) ≤ 62 in §6.1.1 and attributes the upper bound to that paper. [Survey](https://www.combinatorics.org/ojs/index.php/eljc/article/download/DS1/pdf/), [DOI and revision history](https://doi.org/10.37236/21).

The present result lowers the recorded upper bound by one. Its ingredients are the marked-root A/B/D exclusions, a global ticket-counting argument, a direct 346-case C entrance cover, and an elementary reduction of perfect balance to three full-host SAT formulas. The balanced formulas encode support choices and the visible parts of actual critical neighborhoods. The complete argument is in [proof.md](../proof.md).

The critical K15/K16 classifications are known results for which the project supplies its own local Lean proofs and finite certificates; see [classification provenance](CLASSIFICATION_PROVENANCE.md).

The [verification method](TRUST_AND_CERTIFICATION.md) explains the formal mathematical reduction, exact input binding and two-solver computational evidence, and places them in the context of the earlier computational proof.
