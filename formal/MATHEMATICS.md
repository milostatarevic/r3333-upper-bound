# Mathematical dependency map

The final endpoint is [`PricingIntegration.NativeWholeProof.ramsey61`](src/PricingIntegration/NativeWholeProof.lean):

```lean
ramsey61 (h : AllNativeUnsat) : ∀ c : Host, ¬NoMonochromaticTriangle c
```

`Host` is a four-coloring of the actual 61 vertices. `AllNativeUnsat` concerns only the explicitly defined finite CNFs below. The source constructs every mathematical argument connecting a hypothetical good coloring to those formulas.

## Final composition

[`ramsey61_conditional`](src/Ramsey61/Conditional.lean) supplies the outer incidence/graph argument. The endpoint supplies all three mathematical components required by the outer theorem:

| Interface | Proved implementation | Dependency and conclusion |
|---|---|---|
| `abd_supplied_root_selector` | `NativeWholeProof.selector h` | Actual A/B/D roots with high enough incoming mass reach their exact native formulas; their exclusions yield `SelectorX`. |
| `guarded_G_exclusion` | [`GComplete.guarded_G_exclusion`](src/PricingIntegration/GComplete.lean) | Every actual `RegularOverlapGuard` gives a physical finite core; both exhaustive core families are excluded by proved finite relations. This step takes no native UNSAT premise. |
| `physical_C_to_CNF_cover` | [`CComplete.physical_C_to_exact_family`](src/PricingIntegration/CComplete.lean) | An actual `CExteriorWitness`, under the derived selector, yields a satisfying valuation for one exact `concreteFamily i`, `i : Fin 456`. |

The [uniform-host/regular-overlap entrance](src/Ramsey61/GuardedEntrance.lean) is consumed by the outer argument. Absence of a C exterior witness forces synchronized C/E structure, then a uniform common high pair and a regular overlap; G excludes that alternative. The resulting C witness reaches the 456-case family, where `h` gives the contradiction.

## A/B/D to exact native formulas

[`CommonEntrance`](src/CompletionC/CommonEntrance.lean) chooses one global palette and retains complete physical critical cells and the entire four- or five-point low-cell support. [`NativeFamilyJoin.common_native_cover`](src/CompletionC/NativeFamilyJoin.lean) proves support normalization, the 737 support-pair admission, exhaustive matrix coverage, whole-cell coordinate transport, and satisfaction of the native prefix plus **all signed suffix units** by one valuation. Negative support literals are justified by membership biconditionals, not only positive support inclusion.

[`ABNative.actual_native_prefix`](src/PricingABD/ABNative.lean) discharges A/B counter schedules, constant folding, cache references, allocation, and auxiliary valuations. [`DNativePrefix.satisfying_extension`](src/PricingIntegration/DNativePrefixComplete.lean) supplies the original D prefix and preserves every physical edge atom. [`ActualProfileCover`](src/CompletionC/ActualProfileCover.lean) connects these constructions to actual W/H-selected A/B/D roots.

D's two U/U owners are separate. [`UUQPhysicalExtension.selected_split`](src/PricingG/UUQPhysicalExtension.lean) uses the **same supplied physical blocks**, enumerates the complete low K14, retains the original 15/15/16 tail maps and marked vertex, and derives the four/five-support split. [`UUQExactNative.actual_UU_native`](src/PricingG/UUQExactNative.lean) covers precisely 189 P15, 408 restricted D9, and 82 D10 formulas for each Q type. UUT keeps Q16 twisted throughout. `NativeWholeProof.D_selected_excluded` dispatches the same physical witness to this route or the common mixed-D route.

## C and G finite mathematics

`CComplete.normalized_seed_cover` proves the exact 456-seed cover using the actual aligned three-neighborhood construction, simultaneous coordinate/palette transport, and literal seed binding. Its consumer constructs the full CNF valuation, including auxiliaries.

G's physical core cover divides into the 3,600 isomorphic and 10,368 remaining core indices. The structural shared-graph classification, coordinate embeddings, highness requirements, and finite relation contradictions are proved before `GComplete.guarded_G_exclusion` is applied. These finite G checks are not additional SAT assumptions.

## Classification reuse and computational boundary

[`ClassificationAdapter`](src/Ramsey61/ClassificationAdapter.lean) connects the K15/K16 completeness library to actual hosts, preserving vertex and palette maps through `physical_neighborhood_k15` and `physical_neighborhood_k16`. The complete portable build compiles all 32 classification modules from source and replays their 55 included CNF/LRAT pairs.

The final `Case` type is the disjoint sum of [concrete common owner/support/matrix indices](src/PricingIntegration/NativeCommonCases.lean), `Bool × UUQExactNative.Leaf`, and `Fin 456`. The retained native census is 55,016 + 1,358 + 456 = **56,830** inputs. Exact formula-to-archive binding is a separate, hash-pinned reproducibility check. For UUQ, [`emitted_eq`](src/PricingG/UUQEmissionIdentity.lean) proves equality to the cached executable representation, and [the complete input-binding record](checks/joined_bindings/RUN_RESULT.json) matches every complete Lean-emitted input to the retained solver-input hash using the published build.

The remaining explicit hypothesis is the UNSAT of those concrete formulas. Their native solver results supply external computational evidence; `ramsey61` does not kernel-check the large search refutations. Its retained axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`, with `AllNativeUnsat` visible as a theorem parameter. The source-build receipts and complete census/byte bindings provide the accompanying verification evidence.
