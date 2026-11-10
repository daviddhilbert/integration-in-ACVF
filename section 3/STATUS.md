# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12, through Proposition 3.24.

## Verification

The full local project build, inherited QE audit, Section 2 audit and **551
Section 3 declaration type/axiom audits pass** under pinned Lean 4.35.0.
There are 276 generic and 275 actual ACVF heads; these are supporting
components, not 551 numbered paper results. Only `propext`, `Classical.choice`
and `Quot.sound` occur. Every receipt source hash matches. All 201 earlier
actual types match their reviewed checkpoint exactly; all 59 new primitive
batch types match their individually compiled and reviewed snapshots exactly.

`VERIFICATION.json` records this local checkpoint. `CORE-VERIFICATION.json`
selects the 276 generic declarations from the same fresh full audit. Complete
local evidence is retained in `.scratch/local-primitive-551/`. All551 complete CI types match the reviewed local audit exactly. The batch
passed [CI run42900083681](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42900083681)
at source `92f7b0a478d111cde0a23f6b31714abd92f0ed6a`. The preceding 471-head checkpoint passed
[CI run 42884025168](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42884025168)
at proof source `61f65399e4c10915b36bfcaf794d7383b984c962`.

## Numbered results

Eight numbered Section 3 results are checked in the following precise scope:

- **3.2:** `AdjoinBall.lemma_3_2` permits arbitrary real, genuine Gamma and
  ball names. Atomicity is over the original base with the input ball name
  adjoined; nonalgebraicity concerns the output ball imaginary.
- **3.3:** `FullGammaAtomicity.lemma_3_3` preserves atomicity after every finite
  Gamma tuple, for every finite real tuple arity, including mixed VF/RV.
  ACVF(0,0), an original-base definable `δ` and `1 < δ` are explicit.
- **3.4:** `FullGammaRadius.lemma_3_4` proves ball atomicity at original-base
  definable Gamma radii, and for singletons and VF. The ambient complete type
  need not be definable. Only the ball name is adjoined. An extension to
  unrestricted unnamed radii is not claimed.
- **3.6:** `PrimitiveDecomposition.lemma_3_6` decomposes an atomic VF set into
  finitely many nonempty pairwise disjoint primitive bodies, all of the same
  primitive type. Each is an open ball, closed ball or thin annulus, with
  common parent radius and valuative centre. No individual component is
  assumed definable. ACVF(0,0), named `δ` and `1 < δ` are explicit.
- **3.7:** `SameRadiusCoverage` proves whole-ball coverage at the radius of a
  ball contained in an atomic set. The initially unnamed ordinary radius is
  adjoined using 3.3. Singleton/VF conventions are included; the proof does
  not depend on 3.6. The standing ACVF(0,0) and nontrivial value are explicit.
- **3.8:** `PrimitiveImages.lemma_3_8` proves that a full-base definable VF image
  of an atomic set with one primitive component is atomic and has one primitive
  component. The graph need only be defined on the source domain. No image
  component or source parent is assumed individually definable. The same
  standing hypotheses as 3.6 remain explicit.
- **3.9 and 3.10:** `OpenBallConstancy` proves RV-powerset constancy on an atomic
  open ball and on an open subball of an atomic set, for every finite RV arity.
  Full domain graphs and the sequel's open-ball convention are used. The
  subball's radius need not be named initially; 3.3 adjoins it. The standing
  characteristic and nontriviality hypotheses remain explicit.

Section 2's Corollary 2.15 is checked separately, with genuine saturation and
parameter smallness explicit. Corollary 2.34 remains open.

## Geometry behind 3.6 and 3.8

The canonical minimal finite support is unique and its full ball-name family
is definable over the original combined base. The finite proper-subball
non-covering theorem is the already formalized Johnson theorem on the actual
valuation balls. Positive regions, maximal holes, open/closed-kind tests and
radius/valuative-centre graphs retain every valid real code. No chosen centre,
field lift or representative enters the parameter base.

`OrdinaryRadiusFibres` proves the complete radius graph, finite original-base
Gamma image and definability of its occurring values. `UniformRadius` and
`UniformValuativeCentre` prove the common invariants of positive regions,
including singleton/VF exceptions.

`BallEnlargementGeometry` and `NamedClosedHoleCut` exclude a nonmaximal hole:
its intrinsic finite family of named-radius closed enlargements would split
the atomic set. All surviving holes are maximal open subballs of ordinary
closed parents. `AffineArithmetic` supplies parameter-free natural affine
terms; `AffineHoleGeometry` proves representative independence and a finite
full-code transport graph. `AffineHoleCut` uses that graph to rule out two
holes. The result is exactly one maximal open hole in every punctured piece.
`PrimitiveDecomposition` combines these facts with the common invariants.

`PuncturedImageComponents` recovers the source parent from its exact minimal
support. Atomicity and finite proper-subball non-covering force a singleton
family of image regions. `PrimitiveImages` then applies the checked primitive
classification. Original-base definability of the individual canonical pieces
is never assumed.

## Remaining work

Thirteen proof results remain, 3.11–3.19 and 3.21–3.24; 3.20 is a definition.
These comprise seven lemmas, two corollaries and four propositions. The next
result is corrected geometric separation in 3.11, then the function and image
consequences and the closed-image obstruction. Do not count a helper that
assumes missing geometry as a proof of the corresponding numbered statement.

The generic separation core already proves joint inverse-support graphs,
uniform finite-row bounds directly from atomicity, proper inverse supports,
finite/cofinite class traces, intrinsic closed hulls, and a source cut with
infinitely many small quotient classes on both sides. The actual ACVF wrappers
for this route are being checked locally; the assembled 3.11 is not established.
No new saturation or cardinality hypothesis is introduced in this route.

The author approved adding **`R.Nonempty`** to printed 3.11, whose empty
relation is a counterexample. Retain it explicitly; see
[`PAPER-CORRECTIONS.md`](../PAPER-CORRECTIONS.md).

## Build conventions

```sh
lake build
lake env python3 scripts/verify_ci.py
```

The common actual LRV structure and actual Gamma/ball quotients are unchanged.
Freeze original-model sets, functions and presentations before binding a
canonical normalized structure, even with a non-instance `let`. Native
multiplicative valuation order reverses the paper Gamma order. The sequel's
open-ball predicate excludes singleton degeneracies and includes VF explicitly.

Pinned Mathlib and the required predecessor import closure were successfully
built locally after cache access was blocked. They are now available; do not
restart the cold bootstrap. The root imports ACVF-QE and the sequel libraries;
the actual geometry uses the predecessor's pinned Sections 3 and 4 directly.
CI still builds the full predecessor separately. No dependency pin changed.
Compile and audit locally before pushing; use CI for integration confirmation.
HK may supply background proof ideas only: no HK citation or unproved input.
