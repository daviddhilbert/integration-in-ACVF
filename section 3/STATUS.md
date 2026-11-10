# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12. The main structural target is the finite
definable partition with the open-to-open property in Proposition 3.19.
The section continues through Proposition 3.24: mixed-coordinate open-to-open
partitions, component/hole counts, and obstructions to geometric bijections
are also in scope. None of those later statements is marked complete.

## Current scope

The Section 3 library build and all **55 declaration type/axiom audits
passed** under Lean 4.35.0. Only `propext`, `Classical.choice` and `Quot.sound`
occur in their axiom reports. The checked sources contain no `sorry`, `admit`
or custom axiom declarations. This is a certificate for the components below,
not 55 numbered paper results and not completion of Lemma 3.2.

`VERIFICATION.json` records the exact source hashes, compiler, dependency pins
and per-headline axioms. Full compiler output and the freshly compiled audit
source are retained locally in `.scratch/section3-verified/`.

| Component | Source | Scope |
| --- | --- | --- |
| Definition 3.1 | `IntegrationSection3/Atomicity.lean` | Complete-type-generating and atomic sets use actual Mathlib first-order definability over an arbitrary base. The definitions are generic in the language and tuple index. |
| Basic atomicity calculus | Same | Predicate agreement, subset and parameter restriction, no proper nonempty definable subset, equality/disjointness, and definable images. No ACVF or saturation premise is needed. |
| Finite support for Boolean combinations | `IntegrationSection3/BallSupport.lean` | Connects Mathlib's Boolean subalgebra closure to finite membership support. |
| Finite-exception geometry for Lemma 3.2 | Same | A finite Boolean combination of a laminar family splits only finitely many members of any pairwise disjoint subfamily. The containment and disjointness hypotheses are explicit. |
| First-order parametric atomicity | `IntegrationSection3/DefinableFamilies.lean`, `ParametricAtomicity.lean` | Proves parameter promotion, same-base definability of the exceptional indices, their finiteness, and the algebraicity contradiction. C-minimality and laminarity are explicit geometric inputs. The associated-code variant uses a genuinely definable map. |
| Imaginary-index argument | `IntegrationSection3/ImaginaryFamilies.lean` | Full real-preimage definability on an interpreted quotient sort; equality follows from an injective definable membership relation. Proves finite exceptional imaginary indices, same-base algebraicity transfer through a definable partial function, and atomicity under nonalgebraicity of the output imaginary. No chosen representative is named. Actual ball presentation still needs verification. |
| Complete-type argument for Lemma 3.4 | `ImaginaryFamilies.lean` | A member of a definable disjoint family contained in a complete-type-generating set is atomic over its imaginary index. This logical argument needs no C-minimality or nonalgebraicity hypothesis. The actual same-radius family is still needed. |
| Actual ACVF geometry and real-index case | `IntegrationSection3ACVF/Geometry.lean` | Written, pending compilation and five additional type/axiom audits in CI. Uses the predecessor's proved C-minimality and unchanged ball predicates on the canonical normalization. No verification claim yet. |
| Actual imaginary ball presentation and real-base Lemma 3.2 | `IntegrationSection3ACVF/BallPresentation.lean` | Written, pending compilation and eleven further audits. Uses the predecessor's actual open/closed quotients, a surjective full code presentation, proved interpreted equality, proved ball geometry/C-minimality, and nonalgebraicity of the actual output-ball imaginary. It covers real parameter bases; bases containing additional imaginary names are not claimed. |
| Lemma 3.3 over a real base | `IntegrationSection3ACVF/GammaAtomicity.lean` | Written, pending compilation and five further audits. Covers arbitrary finite Gamma parameter tuples and finite mixed output arities, with an explicit original-base definable nontrivial Gamma value. Uses the predecessor's proved tuple definable-point theorem. Full bases containing ball names remain open. |
| Full Lemma 3.2 | Not complete | The imaginary ball-index interpretation and exact imaginary parameter base still need to be connected. The generic theorem is not counted as this missing interpretation. |
| Lemmas 3.3–3.18 and Proposition 3.19 | Not complete | No coverage is claimed by the preceding generic results. |

The tuple carrier can later be restricted to the actual VF/RV sorts. Allowing
a generic first-order language also permits an imaginary expansion, but does
not construct that expansion or prove the required ACVF interpretations.
The paper's Definition 3.1 does not explicitly require nonemptiness; the code
retains this convention and adds nonemptiness when selecting a realization.

## Verification

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
# ACVF bridge and twenty-one additional declarations:
lake env python3 'section 3/verify.py' --acvf
```

The verifier records exact source/pin/compiler identities, checks all current
headline types and their axiom allowlists, and compiles the library import.
Evidence goes in `.scratch/section3-verified/`. A successful incremental build
does not imply every dependency was freshly compiled in that invocation.
The root `IntegrationInACVF.lean` also imports the predecessor; a check of only
this Section 3 library is not a fresh build of that full coordination root.

## Wording issue to resolve before Lemma 3.11

The printed Lemma 3.11 says a definable relation `A` between two atomic balls
cannot have finite-to-one first projection. Taken literally this includes the
empty relation, whose projection is finite-to-one. Its proof uses both
projections being surjective, which requires `A` to be nonempty. Record an
explicit nonemptiness condition before formalizing that headline; no silent
paper correction has been implemented. `StatementChecks.lean` now verifies
the empty relation's definability, product containment and finite fibres.
The author clarification was requested in this session and is still pending.
This does not affect Definition 3.1 or the earlier family arguments.
