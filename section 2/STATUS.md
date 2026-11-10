# Section 2: preliminaries and review

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
[CI run 42789563292](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42789563292).
Only `propext`, `Classical.choice` and `Quot.sound` occur. `VERIFICATION.json`
records the exact checked source identities, compiler and dependency pins.

Corollary 2.34 remains open. The legacy volume-form interfaces in the pinned
predecessor have explicit mathematical inputs, so their import is insufficient
to claim the full concrete measure-preservation assertion here.

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
certificate. The Section 3 core is generic; its pending ACVF bridge uses the
actual C-minimality and ball-quotient sources. References [11] and
[12] in the paper are different papers; do not conflate their numbering.

Standing language corrections are recorded in the pinned predecessor's
`LANGUAGE-ERRATA.md`. No new language or author correction is introduced here.
