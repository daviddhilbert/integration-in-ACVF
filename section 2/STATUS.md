# Section 2: preliminaries and review

The subsequent henselian-support batch passes the full root,inherited QE,
all 41 Section2 and1244 unchanged Section3 type/axiom audits. All27 earlier
Section2 types are unchanged; all14 new complete types match individually
reviewed audits. All22/368 section source hashes and both audit hashes match.
Only the three permitted standard axioms occur. Evidence is archived in
`.scratch/local-henselian-support-41/`, including its own Section2 andSection3
logs and receipts. [CI43004909322](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43004909322) passed after exact full type/source/audit matching.

The five new support modules prove finite Galois immediate-extension
triviality in residue characteristic zero, Hensel descent through actual
Galois fixed fields, henselianity of intermediate fields in an algebraically
closed Galois envelope, residue-independent lifting and the finite residue
degree bound, and lifting of a primitive residue generator. No desired
finite-extension degree equality or graph reference is assumed in these new
theorems. The envelope, approximation and field hypotheses remain explicit.
They do not yet discharge the general finite-extension reference or make
the concrete2.34 bridge unconditional.

Source: arXiv:0809.0473v2, pp. 3–7. Section 1 is introductory and has no
separate proof target. The existing section layout continues to exclude it.

Section 2 mostly recalls the common language and earlier mathematics. Reuse
the pinned Special transformations project and its ACVF-QE dependency. Do not
copy their language or infer that every cited result has identical scope.
Corollaries 2.15 and 2.34 are derived statements in this paper; they are not
automatically discharged merely by importing the predecessor.

`IntegrationSection2/GammaFiniteImage.lean` now derives Corollary 2.15 from
the predecessor's proved `GammaRVFamily.finite_projection`. It covers partial
functions from actual Gamma to RV, over both arbitrary small real bases and
genuine Gamma-named bases. The entire function graph is required to be
definable through its full preimage on nonzero RV representatives. Saturation,
smallness and pure characteristic zero remain explicit. The full project
build and both full type/axiom checks passed in
[CI run 42845510919](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42845510919).
Only `propext`, `Classical.choice` and `Quot.sound` occur. `VERIFICATION.json`
records the exact checked source identities, compiler and dependency pins.

Corollary 2.34 has a concrete descent proof relative to the predecessor's
explicit henselian graph input. `VolumeLiftDescent.corollary_2_34_positive`
proves both actual volume conditions; `corollary_2_34_essential` handles the
essential restrictions of arbitrary original finite-volume RV objects.
`corollary_2_34_of_finite_extension_reference` supplies the graph input from
the exact named finite-extension reference in the predecessor. That reference
remains unproved here, so unconditional 2.34 remains open. A legacy volume-law
interface is not a substitute for this concrete bridge or for that reference.

The 11 new modules and 25 helper/headline declarations use actual definable
nonzero RV forms, full-base finite-volume categories and actual partial
VF/RV Jacobians. The generic RV equation holds off an actual RV-small label
subset; the Gamma equation holds at every essential label. Fixed-label
restriction preserves bijectivity and the actual VF Jacobian. Only finitely
many label coordinates are named internally. The original base, ACVF00,
genuine saturation and homogeneity remain visible through `BaseContext`.
Degree zero follows the category convention.

The full root build, inherited QE, all 27 Section 2 complete type/axiom audits
and all 1,244 unchanged Section 3 audits passed locally. All 25 new complete
types match individually reviewed audits; both earlier Section 2 types are
unchanged. All source and audit hashes match the reviewed checkout; only
`propext`, `Classical.choice` and `Quot.sound` occur. Evidence is archived in
`.scratch/local-volume-descent-27/` with its own Section2 and Section3 logs.
[CI43002045059](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43002045059) passed; complete types and source/audit hashes match the local batch archive and publication checkout. See `VERIFICATION.json` and `HANDOFF.md`.

## Source reuse candidates for Section 3

| This paper | Pinned predecessor source | Review boundary |
| --- | --- | --- |
| Definitions 2.2–2.3: balls and punctures | `Section3/BallGeometry.lean`, ACVF-QE `Enc.lean` | Preserve radius order and the single absorbing RV element. Canonical imaginary ball codes still need a sequel interface. |
| Lemma 2.8: algebraic fibre descent | `Section3/FibreDescent.lean`, `GammaFullDescent.lean` | Real and Gamma bases have separate theorems; check actual base and nonempty-fibre hypotheses. |
| Lemma 2.9: VF algebraicity | `Section3/VFAlgebraicity.lean` | Check the coefficient field and parameter scope. |
| Lemma 2.10: finite RV-to-VF image | `Section3/FiniteImage.lean` | Check canonical-model hypotheses and tuple arity. |
| Lemma 2.11: independence | `Section3/RVIndependence.lean`, Gamma separation modules | Same valuation and same RV class are different relations. |
| Lemmas 2.13–2.14: ball centres | Closed/open/general ball-centre modules in `Section3/` | Generated-base and imaginary-parameter scope must match the cited form. |
| Lemma 2.16: constancy away from finitely many cosets | `Section3/AdditiveCosets.lean`, powerset-family interfaces | The functions are definable relations into a powerset, not arbitrary functions into a new first-order sort. |
| C-minimality used in Lemma 3.2 | `Section3/CMinimal.lean` | Its proved theorem is `SpecialTransformations.Section3.theorem_2_8_c_minimal`; connect its Boolean-combination representation to the sequel's finite support. |

These are source-inspected candidates, not a new combined verification
certificate. The Section 3 core is generic; its checked ACVF bridge uses the
actual C-minimality and ball-quotient sources. References [11] and
[12] in the paper are different papers; do not conflate their numbering.

Standing language corrections are recorded in the pinned predecessor's
`LANGUAGE-ERRATA.md`. No new language or author correction is introduced here.
