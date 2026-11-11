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
| 3.2 | A definable family indexed by ball imaginaries, disjoint output balls, nonalgebraicity of the output-ball imaginary over the original base; atomicity over the index. Checked with additional actual Gamma and ball names. The family and graph use full invariant preimages, and atomicity is over the original base with the input-ball name adjoined. |
| 3.3 | Adjoining every finite tuple of actual Gamma parameters preserves atomicity for mixed VF/RV tuples. Checked over the full real/Gamma/ball base. The definable-point step is derived from intrinsic finite controllers, with ACVF(0,0), a definable `δ` and `1 < δ` explicit. |
| 3.4 | Complete for every actual open/closed ball over the full original base,including arbitrary unnamed radii,singletons andVF,and possibly undefinable complete-type ambients. Genuine saturation,infinite cardinal,small original real base,ACVF00 and an actual nontrivial value are explicit. |
| 3.5–3.8 | Primitive type, canonical punctured-ball decomposition of an atomic unary set, same-radius ball coverage, and one-component preservation under definable images. The predicates, canonical support and full-code positive/hole relations, common radius and valuative centre, intrinsic hole enlargement and affine single-hole argument are checked. Lemma 3.6 now gives the full primitive classification; Lemma 3.8 gives one-component preservation for partial-domain definable VF images. ACVF(0,0) and an original-base definable nontrivial Gamma value remain explicit. Corollary 3.7 is checked directly from 3.3, including singleton and VF cases. |
| 3.9–3.10 | Constancy of powerset-valued RV families on atomic open balls and on open subballs of atomic sets. Checked using full domain graphs over the combined base, derived finite exceptions and integer-translate geometry. The sequel open-ball convention, ACVF(0,0), and a definable nontrivial Gamma value are explicit. |
| 3.11–3.14 | Corrected3.11 geometric separation, both3.12 function restrictions and 3.13 open-ball images are checked over the full base with standing ACVF(0,0) and named nontrivial value explicit. Retain author-approved `R.Nonempty` in 3.11. Lemma 3.14 and its parameter-preserving syntax bridge are checked with the source ball as the only ball imaginary plus original Gamma names; the source radius need not be originally named. See `../PAPER-CORRECTIONS.md`. |
| 3.15 | Complete over the full original real/Gamma/ball base,arbitrary open radii and possibly undefinable complete types,with genuine saturation,infinite cardinal,small original real base,ACVF00 and originally definable nontrivial value. Actual full partial graph; no old-imaginary cardinal bound. |
| 3.16 | Actual Gamma-linearity with coefficient equal to target/source radius ratio is checked over the full original base. Genuine saturation, infinite saturation cardinal, small real base, ACVF00 and named nontrivial delta are explicit. The actual tail order isomorphism, finite shift range and finite controllers are proved; no linearity premise is assumed. |
| 3.17 | The stated exclusion is checked for every given least-linear-radius function. Actual linear beta-subball existence at every smaller radius is proved, including VF source. Original full base, genuine saturation, infinite cardinal, small real base and ACVF00 are explicit; centre/radius codes are named only inside the proof. |
| 3.18 | Actual RV-linearity is checked over the full original base, with genuine saturation, infinite cardinal, small real base, ACVF00 and named nontrivial Gamma value explicit. The map needs only its partial-domain graph and injection; image openness is derived. Finite-fibre means and checked 3.16 give a radius contradiction on a newly chosen atomic RV fibre, replacing the printed endpoint estimate. |
| 3.19 | Complete:actual finite nonempty disjoint original-base definable OpenToOpen partition of an actual VF bijection over the full original base. Same standing scope as3.15; no finiteness or cardinal bound on old imaginary names. |
| 3.20–3.21 | Complete actual coordinate-fibre definition and full uniform finite nonempty disjoint original-base partition for every selected VF coordinate pair of mixed finite tuple injections,with standing saturation,smallness,ACVF00 and originally named nontrivial value. No old-imaginary cardinal bound or local/uniform choice premise. |
| 3.22–3.24 | Lemma 3.22 is complete over the full original interpreted base, for actual finite disjoint thin families and their open-to-open VF bijection. Both component and total actual-hole counts are equal; native residue coordinates, full quotient graph, conservation and general-model normalization are proved. Proposition3.23 is also complete for every distinct actual atomic primitive-shape pair, with full base, ACVF00 and an original-base definable nontrivial Gamma value; it uses actual zero/one hole counts and checked atomic open-to-open maps. Proposition3.24 has a checked literal whole-field identity counterexample; an ordinary closed-parent clarification is pending author approval,and the intended ordinary-parent obstruction remains open. |

No later theorem is counted as proved by generic logical helpers or by an
interface assuming the missing geometry. Characteristic, saturation and
smallness hypotheses must be visible in the final exported types.
