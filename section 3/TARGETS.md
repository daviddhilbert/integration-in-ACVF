# Scope of Sections 1–3

Paper version: arXiv:0809.0473v2. Section 1 is introductory. Section 2 is
reviewed separately, with Corollaries 2.15 and 2.34 as new proof obligations.
Section 3 ends at Proposition 3.24, not Proposition 3.19.

## Parameters and conventions

Section 3 works in the paper's interpreted expansion C•. The additional sort
contains open and closed balls at the indicated base radii. The underlying
base can itself contain imaginary ball names; genuine Gamma names must also
be preserved. A theorem proved only over a real base is a partial scope.
The current full-preimage ball presentation uses the existing predecessor
quotient, which identifies exactly equal underlying sets, and never names a
chosen centre or radius representative in its conclusion.

The C-minimality ball collection may include singleton degeneracies. For
later open-to-open claims, inspect the sequel's own open-ball convention:
`Enc.IsOpenBall` also includes singleton balls by the predecessor's convention.
That broader predicate must not silently be used for a proper open ball in
this paper. VF itself is clopen by the sequel's explicit convention.

## Proof targets

| Statement | Required target and current boundary |
| --- | --- |
| 3.1 | Actual first-order complete-type generation and atomicity, all finite VF/RV tuple arities, arbitrary parameter base. The generic Mathlib definitions and calculus are checked. |
| 3.2 | A definable family indexed by ball imaginaries, disjoint output balls, nonalgebraicity of the output-ball imaginary over the original base; atomicity over the index. The quotient argument and actual real-base instance are checked. Full C• bases remain open. |
| 3.3 | Adjoining every finite tuple of actual Gamma parameters preserves atomicity for mixed VF/RV tuples. Derive the definable-point step from the standing nontrivial base and Gamma geometry; do not assume the atomicity conclusion. |
| 3.4 | Every open/closed ball inside a complete-type-generating unary set is atomic over its ball code. The ambient set need not be definable. The logical disjoint-family argument is checked; the actual additive-coset family is checked. Named-radius and definable-Gamma-radius specializations are undergoing full checks; the full base remains open. |
| 3.5–3.8 | Primitive type, canonical punctured-ball decomposition of an atomic unary set, same-radius ball coverage, and one-component preservation under definable images. Radius, valuative centre and kind must be invariant and definable over the exact base. |
| 3.9–3.10 | Constancy of powerset-valued RV families on atomic open balls and on open subballs of atomic sets. Use full definable graphs and the original-base finite-coset exception theorem. |
| 3.11–3.14 | Geometric separation of atomic balls, function restrictions, open-ball images and the closed-image obstruction. The author approved adding `A ≠ ∅` to 3.11; retain it explicitly. See `../PAPER-CORRECTIONS.md`. |
| 3.15 | Every open ball inside a complete type has open image under a definable function injective on that type. |
| 3.16–3.18 | Gamma-linearity, the local threshold consequence, and the stronger RV-linearity of bijections of atomic open balls. Keep the orders, radii and single absorbing RV element consistent. |
| 3.19 | Finite definable partition of a unary definable bijection into restrictions preserving and reflecting open balls. Both compactness applications require actual saturation and parameter bounds. |
| 3.20–3.21 | The coordinate-fibre definition for mixed arities and its finite definable partition theorem. Reuse predecessor coordinate projections and assembly. |
| 3.22–3.24 | Preservation of component/hole counts for thin punctured balls, nonexistence of the specified geometric bijections, and the punctured closed/open obstruction. The residue-field constructibility and conservation arguments, and ordered-group Euler-characteristic argument, are separate proof obligations. |

No later theorem is counted as proved by generic logical helpers or by an
interface assuming the missing geometry. Characteristic, saturation and
smallness hypotheses must be visible in the final exported types.
