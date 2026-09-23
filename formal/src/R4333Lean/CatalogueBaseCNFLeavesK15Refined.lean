import R4333Lean.CatalogueBaseCNF

/- Kernel-checked refined K15 extension leaves. -/
namespace R4333.CatalogueBaseCNF

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

checked_lrat_proof k15_deficient_split_0_unsat (k15BadDeficientLeaf 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_split_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_split_0.lrat")

checked_lrat_proof k15_deficient_split_3_unsat (k15BadDeficientLeaf 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_split_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_split_3.lrat")

checked_lrat_proof k15_deficient_1_blue_0_2_3_unsat (k15BadDeficientRefined 1 0 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_2_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_2_3.lrat")

checked_lrat_proof k15_deficient_1_blue_0_3_2_unsat (k15BadDeficientRefined 1 0 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_3_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_3_2.lrat")

checked_lrat_proof k15_deficient_1_blue_0_4_1_unsat (k15BadDeficientRefined 1 0 4)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_4_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_0_4_1.lrat")

checked_lrat_proof k15_deficient_1_blue_1_1_3_unsat (k15BadDeficientRefined 1 1 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_1_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_1_3.lrat")

checked_lrat_proof k15_deficient_1_blue_1_2_2_unsat (k15BadDeficientRefined 1 1 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_2_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_2_2.lrat")

checked_lrat_proof k15_deficient_1_blue_1_3_1_unsat (k15BadDeficientRefined 1 1 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_3_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_3_1.lrat")

checked_lrat_proof k15_deficient_1_blue_1_4_0_unsat (k15BadDeficientRefined 1 1 4)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_4_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_1_4_0.lrat")

checked_lrat_proof k15_deficient_1_blue_2_0_3_unsat (k15BadDeficientRefined 1 2 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_0_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_0_3.lrat")

checked_lrat_proof k15_deficient_1_blue_2_1_2_unsat (k15BadDeficientRefined 1 2 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_1_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_1_2.lrat")

checked_lrat_proof k15_deficient_1_blue_2_2_1_unsat (k15BadDeficientRefined 1 2 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_2_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_2_1.lrat")

checked_lrat_proof k15_deficient_1_blue_2_3_0_unsat (k15BadDeficientRefined 1 2 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_3_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_2_3_0.lrat")

checked_lrat_proof k15_deficient_1_blue_3_0_2_unsat (k15BadDeficientRefined 1 3 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_0_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_0_2.lrat")

checked_lrat_proof k15_deficient_1_blue_3_1_1_unsat (k15BadDeficientRefined 1 3 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_1_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_1_1.lrat")

checked_lrat_proof k15_deficient_1_blue_3_2_0_unsat (k15BadDeficientRefined 1 3 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_2_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_1_blue_3_2_0.lrat")

checked_lrat_proof k15_deficient_2_blue_0_1_4_unsat (k15BadDeficientRefined 2 0 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_1_4.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_1_4.lrat")

checked_lrat_proof k15_deficient_2_blue_0_2_3_unsat (k15BadDeficientRefined 2 0 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_2_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_2_3.lrat")

checked_lrat_proof k15_deficient_2_blue_0_3_2_unsat (k15BadDeficientRefined 2 0 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_3_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_0_3_2.lrat")

checked_lrat_proof k15_deficient_2_blue_1_0_4_unsat (k15BadDeficientRefined 2 1 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_0_4.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_0_4.lrat")

checked_lrat_proof k15_deficient_2_blue_1_1_3_unsat (k15BadDeficientRefined 2 1 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_1_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_1_3.lrat")

checked_lrat_proof k15_deficient_2_blue_1_2_2_unsat (k15BadDeficientRefined 2 1 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_2_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_2_2.lrat")

checked_lrat_proof k15_deficient_2_blue_1_3_1_unsat (k15BadDeficientRefined 2 1 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_3_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_1_3_1.lrat")

checked_lrat_proof k15_deficient_2_blue_2_0_3_unsat (k15BadDeficientRefined 2 2 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_0_3.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_0_3.lrat")

checked_lrat_proof k15_deficient_2_blue_2_1_2_unsat (k15BadDeficientRefined 2 2 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_1_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_1_2.lrat")

checked_lrat_proof k15_deficient_2_blue_2_2_1_unsat (k15BadDeficientRefined 2 2 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_2_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_2_1.lrat")

checked_lrat_proof k15_deficient_2_blue_2_3_0_unsat (k15BadDeficientRefined 2 2 3)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_3_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_2_3_0.lrat")

checked_lrat_proof k15_deficient_2_blue_3_0_2_unsat (k15BadDeficientRefined 2 3 0)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_0_2.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_0_2.lrat")

checked_lrat_proof k15_deficient_2_blue_3_1_1_unsat (k15BadDeficientRefined 2 3 1)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_1_1.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_1_1.lrat")

checked_lrat_proof k15_deficient_2_blue_3_2_0_unsat (k15BadDeficientRefined 2 3 2)
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_2_0.cnf")
  (include_str "../r4333_upper/catalogue_base_cnf/k15_deficient_2_blue_3_2_0.lrat")

#print axioms R4333.CatalogueBaseCNF.k15_deficient_2_blue_3_2_0_unsat

end R4333.CatalogueBaseCNF
