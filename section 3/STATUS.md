# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12, through Proposition 3.24.

## Verification

The full local project build, inherited QE audit, Section 2 audit and **600
Section 3 declaration type/axiom audits pass** under pinned Lean 4.35.0.
There are 276 generic and 324 actual ACVF heads. These are supporting
components, not 600 numbered results. Every source hash matches. All551 prior
complete theorem types are unchanged; all 49 new separation-batch types match
their individually compiled and manually reviewed snapshots exactly. Only
`propext`, `Classical.choice` and `Quot.sound` occur.

`VERIFICATION.json` records the local 600-head checkpoint. `CORE-VERIFICATION.json`
selects its 276 generic heads. Complete evidence is in
`.scratch/local-separation-600/`. New CI confirmation is pending. The previous
551-head primitive checkpoint passed
[CI run 42900083681](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42900083681)
at proof `92f7b0a478d111cde0a23f6b31714abd92f0ed6a`; all 551 complete CI types
and all 105 source hashes matched the reviewed local evidence before promotion
to main at receipt commit `b71e2eb18ab68c46e34fecf111f33992c7eda7b6`.

## Numbered results

Eleven numbered Section 3 results are checked in the following precise scope:

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

- **3.11, corrected:** `Separation.lemma_3_11` proves that a nonempty definable
  relation from an atomic open ball to an atomic closed ball of radius less
  than infinity, or an atomic thin annulus, cannot have finite first-coordinate
  fibres. `R.Nonempty` is explicit. Neither ball radius must be originally
  named. Full real/Gamma/ball bases, ACVF(0,0) and named nontrivial `δ` are
  retained; no extra saturation premise is added.
- **3.12:** `SeparationFunctions` proves both function obstructions: no map
  from the atomic open ball to the stated finite-radius closed/thin target,
  and no finite-to-one map in the reverse direction. The reverse statement
  also handles singleton closed sources.
- **3.13:** `OpenImages.lemma_3_13` proves that a definable VF image of an atomic
  open ball is constant or an atomic open ball, using the checked primitive
  image classification and separation. Full partial-domain graphs and the
  unchanged parameter base are used.

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

## Checked separation geometry

The actual inverse-image support graph retains all codes, and atomicity
bounds finite relation rows uniformly. Proper canonical inverse-support balls
have genuine minimal native closed hulls inside the open source. Their radius
is described by the full original-base span graph;3.3 makes that radius
constant across the infinite family of target maximal open classes. A source
cut has infinitely many smaller quotient classes on both sides, contradicting
the finite/cofinite trace theorem. Trace definability is proved after naming
the cut, without assuming atomicity over that enlarged base.

## Remaining work

Ten proof results remain,3.14–3.19 and3.21–3.24;3.20 is a definition. They
comprise five lemmas, one corollary and four propositions. Section 2's2.34 is
open separately. Lemma3.4 currently covers original-base definable radii plus
singleton/VF; its unrestricted unnamed-radius extension is also still needed
for the full3.15 claim. Do not count a named-radius wrapper as unrestricted3.15.

The next target is3.14. Its restriction that only the source ball imaginary
is needed to define the target must remain explicit. Polynomial escape,
coefficient-field root avoidance and elimination of a ball name in favour of
its centres are being connected to parameter-preserving quantifier elimination.
The finite two-variable polynomial support and Gamma-parameter specialization
bridges remain to be supplied. No interface assuming those bridges counts
as a proof of 3.14.

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
