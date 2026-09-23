#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p .lake/build/lib/lean/R4333Lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CheckedLRAT.olean R4333Lean/CheckedLRAT.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/Basic.olean R4333Lean/Basic.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/FiniteColorCNF.olean R4333Lean/FiniteColorCNF.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CatalogueBaseLiteral.olean R4333Lean/CatalogueBaseLiteral.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CatalogueBaseCNF.olean R4333Lean/CatalogueBaseCNF.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CatalogueBaseCNFLeavesK16Refined.olean R4333Lean/CatalogueBaseCNFLeavesK16Refined.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CatalogueBaseCNFSemantics.olean R4333Lean/CatalogueBaseCNFSemantics.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/JoinC5.olean R4333Lean/JoinC5.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/Obstruction.olean R4333Lean/Obstruction.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/Attaching61Arithmetic.olean R4333Lean/Attaching61Arithmetic.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/Attaching61.olean R4333Lean/Attaching61.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ThreeColorCatalogue.olean R4333Lean/ThreeColorCatalogue.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ColorRelabel.olean R4333Lean/ColorRelabel.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/K16CommonCertificate.olean R4333Lean/K16CommonCertificate.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ClebschCompletionData.olean R4333Lean/ClebschCompletionData.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ClebschCompletionCNF.olean R4333Lean/ClebschCompletionCNF.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ClebschCompletionSemantics.olean R4333Lean/ClebschCompletionSemantics.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CriticalTemplates.olean R4333Lean/CriticalTemplates.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ClebschCompletionClassification.olean R4333Lean/ClebschCompletionClassification.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/ClebschUniqueness.olean R4333Lean/ClebschUniqueness.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/K16CatalogueFromSRG.olean R4333Lean/K16CatalogueFromSRG.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/NeighborhoodThreeColor.olean R4333Lean/NeighborhoodThreeColor.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CriticalTemplateDeletionData.olean R4333Lean/CriticalTemplateDeletionData.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CriticalTemplateDeletion.olean R4333Lean/CriticalTemplateDeletion.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/K15Extension.olean R4333Lean/K15Extension.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CriticalTemplateRestriction.olean R4333Lean/CriticalTemplateRestriction.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CatalogueBaseCNFLeavesK15Refined.olean R4333Lean/CatalogueBaseCNFLeavesK15Refined.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/K15DeficientCertificate.olean R4333Lean/K15DeficientCertificate.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/K15Catalogue.olean R4333Lean/K15Catalogue.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CataloguedNeighborhood.olean R4333Lean/CataloguedNeighborhood.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/Attaching61Reduction.olean R4333Lean/Attaching61Reduction.lean
lake env lean -j4 -o .lake/build/lib/lean/R4333Lean/CriticalCatalogues.olean R4333Lean/CriticalCatalogues.lean
