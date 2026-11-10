# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12. This section continues through
Proposition 3.24. Its main open-to-open partition theorem is Proposition 3.19.

## Verified scope

The full project build and **257 Section 3 declaration type/axiom audits
passed** in [CI run 42825054208](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42825054208)
at source `2792396a6ad887fd82430fb4f7d1d4cd5371fb74` under Lean 4.35.0.
There are 116 generic declarations and 141 actual ACVF declarations. These
are component audits, not 257 numbered paper results. Only `propext`,
`Classical.choice` and `Quot.sound` occur. The checked sources have no
placeholders or custom axioms.

- **Lemma 3.2:** arbitrary additional genuine real, Gamma and ball names.
  `AdjoinBall.lemma_3_2` concludes atomicity over the original interpreted
  base with the input-ball name adjoined. Nonalgebraicity concerns the
  output-ball imaginary. Full invariant preimages are used throughout.
- **Lemma 3.3:** `FullGammaAtomicity.lemma_3_3` covers every finite Gamma
  tuple and every finite real tuple arity, hence mixed VF/RV tuples. The
  base may already contain Gamma and ball names. ACVF(0,0), an original-base
  definable value `δ`, and `1 < δ` are explicit. The definable-point theorem
  is proved over that exact base, using an intrinsic minimal controller.
- **Lemma 3.4:** `FullGammaRadius.lemma_3_4` covers open/closed balls at
  every Gamma radius definable over the original combined base, as required
  for the paper's C• ball sort. Singleton and VF cases are also checked.
  The ambient complete-type-generating set need not be definable. The
  conclusion is atomicity with the actual ball name adjoined; neither a
  centre nor a radius representative is named.
- **Lemma 3.9 and Corollary 3.10:** `OpenBallConstancy.lemma_3_9_open` and
  `corollary_3_10_open` cover all finite RV output arities and full graphs
  on the stated domains, over the combined base. They use the sequel's
  open-ball convention, including the vacuous whole-field case. Corollary
  3.10 does not require its subball radius definable over the original base:
  it first adjoins that radius using 3.3. Finite exceptions and infinitely
  many small-ball classes are derived internally. ACVF(0,0) and the standing
  original-base definable nontrivial value remain explicit.
- **Definition 3.5 and the initial step of 3.6:** `PaperBalls.lean` encodes
  the sequel's ball kinds, actual-Gamma radius/valuative-centre predicates
  and common primitive type. `PuncturedGeometry.definable_punctured_decomposition`
  proves a finite disjoint decomposition into nonempty balls minus finitely
  many disjoint proper holes. It does not assert original-base definability
  of each component or equality of primitive types.

## Remaining work

Lemma 3.6's canonical primitive classification and Lemmas 3.7–3.8 remain open.
So do the geometric separation in corrected Lemma 3.11 and the subsequent
image, linearity, open-to-open, component-count and bijection results through
Proposition 3.24. No such result is counted as proved by a helper that assumes
its missing geometry. Section 2's Corollary 2.34 remains open separately.

The next target is a canonical finite support for a definable VF set. Prove
uniqueness using the pinned Johnson finite-proper-subball non-covering theorem,
then recover original-base definability from the intrinsic minimal-support
formula. This must precede the primitive-radius, valuative-centre and hole
classification arguments. Keep all ball-code preimages invariant.

## Current continuation

`MinimalBallSupport.lean` has passed the local 133-declaration core audit.
It proves existence and uniqueness of minimal finite supports in a laminar
family with the explicit finite-proper-subball non-covering property.
`CanonicalBallSupport.lean` supplies the actual ACVF bridge using the already
formalized pinned Johnson theorem, with nontriviality derived from a Gamma
value greater than one. That new actual module is awaiting CI. `SupportFormulas.lean` now proves original-base definability of the fixed-length
support family and its identification with the minimal support. Its seven
new complete types and standard axioms passed that local core audit. `BallCodeGeometry.lean` and `CanonicalSupportFamily.lean` now implement that
actual ball-code bridge and the original-base canonical family. Their full
CI build and audits are pending; the primitive
classification is not yet established. The fixed canonical support now also
covers the VF set and yields disjoint positive regions without inserting a
new parent; both generic steps passed the local core audit. `VERIFICATION.json` remains the full
257-declaration checkpoint, while `CORE-VERIFICATION.json` records the new
local core and its exact input hashes.

## Verification evidence

`VERIFICATION.json` records compiler, dependency pins, all checked source
hashes and per-declaration axioms for the 257-declaration checkpoint.
The full checkpoint contains 116 generic audits; the current local core
receipt may include the explicitly described continuation above. Complete diagnostics, explicit exported definitions/types and
compact type output are in the linked artifact and
`.scratch/ci-2792396-section3/`. Every receipt input hash was compared with
the committed source before publication. Dependencies may be reused from
pinned caches; the full root and new modules were checked by the CI build.

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
lake env python3 'section 3/verify.py' --acvf
```

The unchanged common LRV structure supplies the actual Gamma and ball
quotients. Raw first-order definability is interpreted in its canonical
normalization. Freeze original-model sets and carriers before binding that
normalized structure, which itself participates in Lean instance search.
Definition 3.1 retains the paper's empty-set convention; nonemptiness is
added when choosing a realization.

## Accepted correction to Lemma 3.11

The printed statement includes the empty relation, whose first projection
is finite-to-one. The author approved adding `A ≠ ∅` on November 10, 2026;
see [`PAPER-CORRECTIONS.md`](../PAPER-CORRECTIONS.md).
`StatementChecks.lean` checks the counterexample and proves that a nonempty
definable relation between complete types has both projections surjective.
The corrected geometric statement remains open.
