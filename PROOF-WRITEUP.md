# Writeup of substantially different proofs

Requested by the author on November 10, 2026 (America/Los_Angeles).
**After formalization of the whole paper is complete**, prepare a mathematical
writeup of proofs that differ substantially from those in arXiv:0809.0473v2.
This is a future deliverable for the whole paper, not just Sections 1–3.

Keep this ledger current as results are completed. The final writeup should
explain the mathematical argument in ordinary prose and include:

- The numbered statement and its exact hypotheses or author-approved correction.
- A brief account of the paper's proof and the substantive difference.
- The complete replacement argument, including important intermediate lemmas.
- Why the replacement was chosen and any change in scope or assumptions.
- Links to the final checked Lean declarations and verification checkpoint.

Distinguish mathematical changes from routine encoding, syntax and compiler
work. Recheck each candidate against the final proof before including it.
Preserve the author's existing citation policy; consultation for ideas does
not authorize a new cited theorem or unproved input.

## Current ledger

| Result | Candidate difference | Current state |
| --- | --- | --- |
| Corrected 3.11 | The checked proof uses atomic uniform finite-fibre bounds, canonical inverse supports, intrinsic closed hulls and finite/cofinite quotient traces. Review the exact difference from the printed compactness/cut argument for the final writeup. Keep the approved nonemptiness correction separate from proof differences. | Verified on main; inspect `section 3/IntegrationSection3ACVF/Separation.lean` and its supporting modules. |
| 3.4 and 3.15, real/Gamma-base scope | Replace the new ball's centre by the tested point and leave its radius as an RV variable. A finite original-base polynomial obstacle set controls all RV parameters; the possibly undefinable complete type excludes that set. This supplies unnamed-radius ball atomicity, then open images via 3.13. | Checked in the full 805-head local audit and CI 42949057513; every complete type and source hash matches. This remains the saturation-free real/Gamma proof. Full-base open-ball3.4/3.15 is now supplied by the separate finite-hitting replacement below. Inspect `CompleteTypeRVProfiles`, `SelfCentredBallProfiles`, `OpenCompleteTypeAtomicity` and `CompleteTypeOpenImages`. |
| Full-base3.4 and3.15 | For a putative ball-indexed cut,construct finite hitting points for its full-base definable splitting-ball family using internal real-code compactness and C-minimal finite support. Intrinsic maximal membership profiles have finitely many disjoint terminal classes; finite proper-subball non-covering makes the inner ball one whole class. Checked disjoint-family atomicity contradicts the cut,then3.13 gives the open image. This replaces the printed fixed-radius step without extending an undefinable type over auxiliary parameters. | Checked in the fresh full969-head local audit; all943 published types unchanged and all26 new types match individual reviewed audits. CI42967337352 passed; all complete types and source hashes match. Full original base; genuine saturation,infinite cardinal,small real base,ACVF00 and a nontrivial value explicit(originally definable for3.15). The unnamed closed-ball case is now included in CompleteTypeBallAtomicity.lemma_3_4,checked in the983-head local audit and CI42968768615,with all full types and hashes matched. Add ClosedCompleteTypeRVProfiles,ClosedSelfCentredBallProfiles,RealBallAtomicity andSplittingBallFamilyHitting to the final comparison. Inspect FiniteBallProfiles,TerminalBallCover,BallProfileDefinability,FiniteHittingAtomicity,RealSplittingBallAvoidance,SplittingBallHitting,FullOpenCompleteTypeAtomicity andFullCompleteTypeOpenImages. |
| 3.16 | The constant Gamma shift is proved using continuity of an order isomorphism, finite image, local constancy and finite order controllers, followed by identification of the radius ratio. This supplies an explicit argument valid in a non-Archimedean value group. | Verified on main; inspect `GammaShiftConstancy`, `FiniteControllerLocal`, `GammaTailShift` and `GammaLinearity` in `section 3/IntegrationSection3ACVF/`. Genuine saturation and small-base hypotheses remain explicit. |
| 3.17 | The small atomic subball is constructed through real-point saturation, a nonalgebraic interpreted-family index and checked 3.2. Assess whether this is substantive enough for the final writeup or supporting detail for the paper's argument. | Verified on main; inspect `SaturatedInterpretedFamilies`, `AtomicBallFamilyChoice`, `LinearSubballSpecialization` and `LinearRadiusThreshold`. |
| 3.18 | Definable finite-fibre means make an affine-error map constant or injective on a newly chosen atomic RV fibre. A pair with a different coefficient rules out constancy. Checked Gamma-linearity then forces an image radius incompatible with the strict value bound: the atomic image would contain zero. This replaces the printed endpoint argument. | The complete `RVLinearity.lemma_3_18` is checked in the fresh full 794-head local integration audit and CI 42947193955; all complete types and source hashes match. Keep genuine saturation, infinite cardinal, small real base, ACVF00 and the original-base named nontrivial Gamma value explicit. |
| 3.22 | Finite-field Frobenius and ACF transfer prove arbitrary definable self-map surjectivity. Definable finite patches conserve finite complements; tagged-line comparison gives components and holes directly, replacing the printed regular-injection conservation step. Actual residue coordinates and the full induced graph connect this to the original ball families. | Complete ThinFamilyConservation.lemma_3_22 is checked in the full 914-head local audit and CI 42960151159; every complete type and source hash matches. Full original interpreted base and actual finite counts; no canonical-model restriction, saturation or ACVF00 premise. Inspect ACFDefinableInjection, CofiniteDefinableInjection, TaggedCofiniteConservation, ThinComponentConservation and ThinFamilyConservation with their native coordinate and normalization bridges. |

Add entries from later sections as their proofs are completed. The final
selection and writeup must describe the final implementation, omitting
abandoned approaches unless they explain a mathematical choice.

## 3.21 comparison note

CoordinatePartitions.proposition_3_21 follows the paper's compactness and
finite refinement strategy. The formal development makes the validity
predicate,real-label promotion with invariant code hulls,and full-graph
gluing explicit. Simultaneous Boolean refinement replaces iterative pair
refinement,but does not constitute a substantially different mathematical
proof. No standalone replacement writeup is currently required for3.21.
Local1042-head audit and CI42974291389 passed; exact full type/source/audit hashes matched. The3.4 and3.18 replacement entries
remain relevant for the eventual whole-paper writeup.
