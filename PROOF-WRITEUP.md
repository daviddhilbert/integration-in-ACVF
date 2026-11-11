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
| 3.4 and 3.15, real/Gamma-base scope | Replace the new ball's centre by the tested point and leave its radius as an RV variable. A finite original-base polynomial obstacle set controls all RV parameters; the possibly undefinable complete type excludes that set. This supplies unnamed-radius ball atomicity, then open images via 3.13. | Checked in the full 805-head local audit and CI 42949057513; every complete type and source hash matches. The extension with old ball parameters remains open; do not describe the unrestricted result as complete. Inspect `CompleteTypeRVProfiles`, `SelfCentredBallProfiles`, `OpenCompleteTypeAtomicity` and `CompleteTypeOpenImages`. |
| 3.16 | The constant Gamma shift is proved using continuity of an order isomorphism, finite image, local constancy and finite order controllers, followed by identification of the radius ratio. This supplies an explicit argument valid in a non-Archimedean value group. | Verified on main; inspect `GammaShiftConstancy`, `FiniteControllerLocal`, `GammaTailShift` and `GammaLinearity` in `section 3/IntegrationSection3ACVF/`. Genuine saturation and small-base hypotheses remain explicit. |
| 3.17 | The small atomic subball is constructed through real-point saturation, a nonalgebraic interpreted-family index and checked 3.2. Assess whether this is substantive enough for the final writeup or supporting detail for the paper's argument. | Verified on main; inspect `SaturatedInterpretedFamilies`, `AtomicBallFamilyChoice`, `LinearSubballSpecialization` and `LinearRadiusThreshold`. |
| 3.18 | Definable finite-fibre means make an affine-error map constant or injective on a newly chosen atomic RV fibre. A pair with a different coefficient rules out constancy. Checked Gamma-linearity then forces an image radius incompatible with the strict value bound: the atomic image would contain zero. This replaces the printed endpoint argument. | The complete `RVLinearity.lemma_3_18` is checked in the fresh full 794-head local integration audit and CI 42947193955; all complete types and source hashes match. Keep genuine saturation, infinite cardinal, small real base, ACVF00 and the original-base named nontrivial Gamma value explicit. |
| 3.22, supporting pure-field conservation | Prove surjectivity of arbitrary definable injective self-maps by finite-field Frobenius, finite restrictions and ACF first-order transfer. Definable finite patches then prove conservation of finite complements. | The pure-field components are checked in the full 824-head local audit and CI 42952242946; every complete type and source hash matches. The actual ball-quotient and component/hole bridges remain open; do not describe full 3.22 as established. Inspect `ACFDefinableInjection`, `CofiniteDefinableInjection`, `CofiniteDefinableBijection` and their supporting modules. |

| 3.22, supporting residue-field and ball-quotient components | Use definable Dedekind finiteness and finite patching to conserve both components and holes of finite tagged affine-line unions. Actual residue coordinates identify maximal open classes and finite holes of each closed parent. | Components checked in the full 855-head local audit and CI 42954891823; every complete type and source hash matches. The full affine LRV graph, intrinsic maximal classes and a generic induced-bijection graph are additionally checked in the full 871-head local audit and CI 42956568397, with every complete type and source hash matched. Finite-family coordinate assembly and final graph application remain open; do not describe the full lemma as established. Inspect `TaggedCofiniteConservation`, `ResidueTaggedConservation`, `BallResidueChart`, `ResidueBallClasses` and `ResiduePunctures`. |

Add entries from later sections as their proofs are completed. The final
selection and writeup must describe the final implementation, omitting
abandoned approaches unless they explain a mathematical choice.
