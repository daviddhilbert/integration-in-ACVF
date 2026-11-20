# Section 2: preliminaries and review

**Weighted measured-zero correction checked.**
`WeightedZeroVolumeDescent.corollary_2_34_zero_weighted` uses the actual
published predecessor category and proves exact RV-form preservation on
all zero-degree points. It retains the supplied ordinary label map.
The new module, its four complete types/axiom reports and Section 2 Library
passed under predecessor `25852c85a31c67069b148bd31348128318303510`.
The full Section 2 verifier passed all 72 reports; only the three allowed
standard axioms occur. Evidence is in `VERIFICATION.json` and
`verification/hk-zero/`. Existing positive-degree descent and 2.15 remain.

Source: arXiv:0809.0473v2, pp. 3–7. Section 1 is introductory. The numbered
section layout continues to exclude it. The shared language and pinned
predecessor are reused; source types and hypotheses are checked separately
from bibliographic citations.

## Corollary 2.15

`GammaFiniteImage.lean` derives both real-base and genuine Gamma-named-base
versions from the checked predecessor finite-projection theorem. The full
invariant graph, genuine saturation, small real base and ACVF00 remain
explicit. Both complete theorem types are unchanged in the current audit.

## Corollary 2.34

`VolumeDescentTheorem.lean` exports `IntegrationInACVF.Section2.corollary_2_34`
for actual essential isomorphisms of arbitrary original finite-volume RV
objects in positive degree, and `corollary_2_34_nonzero` for nondegenerate
objects. The all-degree entry point is
`VolumeDescentAllDegrees.corollary_2_34_all_degrees_weighted` (November 19,
2026): its degree-zero branch is the weighted upstream theorem above, with
its actual pointwise measure equation, and its positive branches are the
legacy ones. The legacy `VolumeDescentAllDegrees.corollary_2_34_all_degrees`
keeps its type, but its PUnit zero branch concludes `True`; do not use it as
the all-degree statement.

The conclusion is the two actual volume conditions on the supplied genuine
underlying RV isomorphism. The RV equation holds off a definable RV-small
label subset; the Gamma equation holds at every essential label. The lift
is an actual full-base definable bijection, label compatibility is explicit,
and measure preservation uses the actual partial VF Jacobian off an actual
VF-small exception. Canonical-model and predecessor `BaseContext` standing
assumptions remain visible.

No graph, finite-extension reference, Jacobian-comparison law, Gamma
compatibility law or desired degree equality is an extra premise in the
final theorem. `ConstructedGaussGraph.graph_input` is proved for every
algebraically closed field; its actual ACVF adapter assumes only ACVF.
The construction supplies all embedded finite-extension cases needed by the
predecessor. The old universal `FiniteHenselianExtensionReference` is not
claimed as a separate theorem and is no longer needed by 2.34.

The RV and Gamma proofs are independent. Fixed-label fibre avoidance and
actual Jacobian uniqueness give the generic RV equation. Actual finite
volume fibres pull its exceptional set back to labels. Restricting the
lifted bijection to every fixed label, preserving its derivative charts and
using constant-value polydisc descent gives the pointwise Gamma equation.
The false unrestricted Gamma clause of predecessor 9.15 is not used.

The algebraic input is proved from actual Hensel roots and Galois fixed
fields, all-embedding trace, residue-independent lifts and a primitive
residue generator. The primitive subextension has the residue degree and
surjects onto the residue field. Agreement of values and residues makes
the remaining extension immediate; its trace kernel is zero, so its degree
is one. Field-image and scalar transport are explicitly constructed.
No new outside reference or HK theorem is a proof input. The referee
manuscript supplied no assertion, correction or citation as a proof input.

## Verification

The full root, inherited QE, all 68 Section 2 and 1,244 unchanged Section 3
audits pass locally. All 54 previous Section 2 complete types are unchanged;
all 14 new complete types match individual reviewed audits. All 41/368
source hashes and both audit hashes match the checked checkout. Only
`propext`, `Classical.choice` and `Quot.sound` occur.

Evidence is archived in `.scratch/local-closed-volume-68/`, including its
own Section2 and Section3 logs and receipts. [CI 43010073720](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43010073720) passed.
All complete types and source/audit hashes match the reviewed local batch
and publication checkout. See `VERIFICATION.json`, `HANDOFF.md` and `REUSE-SURVEY.md`.
The earlier conditional volume interfaces remain available with unchanged
types; they are superseded as the final entry points by the proved wrappers.
