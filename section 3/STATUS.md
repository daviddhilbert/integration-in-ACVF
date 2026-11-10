# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12. This section continues through
Proposition 3.24. Its main open-to-open partition theorem is Proposition 3.19.

## Verified scope

The full project build and **360 Section 3 declaration type/axiom audits
passed** in [CI run 42845510919](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42845510919)
at source `2a3b835c341e28f1662441bb84c1f8cda89b5fbe` under Lean 4.35.0.
There are 159 generic declarations and 201 actual ACVF declarations. These
are component audits, not 360 numbered paper results. Only `propext`,
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

- **Canonical finite support:** `CanonicalSupportFamily.exists_definable_canonical_support`
  proves that every set of VF points definable over the combined base has a
  unique minimal finite support by actual balls, and that the full family
  of those ball imaginaries is definable over the original base. The finite
  proper-subball non-covering input is derived from the already formalized
  Johnson theorem. A Gamma value greater than one supplies ambient
  nontriviality; no chosen support tuple, centre or representative enters
  the base. This is a prerequisite for 3.6, not its primitive classification.

- **Definable positive decomposition and holes:**
  `CanonicalRegions.exists_definable_positive_decomposition` proves that the
  positive parents form a finite original-base definable family, their
  nonempty disjoint regions partition A, and their maximal proper holes are
  actual pairwise disjoint balls. `CanonicalHoles.holes_definable` proves
  original-base definability of the joint hole/parent relation through all
  real codes of both ball names. No primitive-type equality is asserted.

- **Kind and invariant geometry:** `BallKindPredicates` proves original-base
  definability of the actual open/closed-kind tests, using all valid charts.
  `AtomicCanonicalRegions.uniform_unpunctured` proves common puncture status
  of the positive regions inside a complete type. `PaperBallInvariants`
  proves radius existence and uniqueness, including singleton and VF cases;
  uniqueness displays `δ > 1`. `ValuativeCentreGeometry` proves centre
  existence on balls and uniqueness on nonempty VF sets. Constancy of
  radius across the positive family remains open.

- **Common valuative centre:** `UniformValuativeCentre.exists_common_centre`
  proves that every canonical positive parent of a definable complete type
  has the same actual valuative centre, including the infinity case. The
  full ordinary-RV graph, its finite Gamma image and each occurring ordinary
  value are definable over the original base. No RV representative or
  component centre is named there. The empty positive family is covered.

- **Corollary 3.7:** `SameRadiusCoverage.corollary_3_7_open` and
  `corollary_3_7_closed` prove same-radius ball coverage at every VF point
  of an atomic set, including singleton and VF cases. The ordinary Gamma
  radius need not be definable over the original base: adjoining it preserves
  atomicity by checked 3.3, then whole-coset coverage is definable. This
  direct proof uses no open 3.6 classification. ACVF(0,0), an original-base
  definable nontrivial Gamma value and `1 < δ` are explicit.

## Remaining work

Lemma 3.6's canonical primitive classification and Lemma 3.8 remain open.
So do the geometric separation in corrected Lemma 3.11 and the subsequent
image, linearity, open-to-open, component-count and bijection results through
Proposition 3.24. No such result is counted as proved by a helper that assumes
its missing geometry. Section 2's Corollary 2.34 remains open separately.

The next targets are the invariant radius graph, its finite image and
common radius, then nonmaximal-hole enlargement and the multiple-hole
contradiction. The canonical support, positive regions and maximal holes are definable over the
original combined base. Individual component definability is not assumed.

## Verification evidence

`VERIFICATION.json` records compiler, dependency pins, all checked source
hashes and per-declaration axioms for the 360-declaration checkpoint.
`CORE-VERIFICATION.json` records the fresh local 270-declaration core audit. Complete diagnostics, explicit exported
definitions/types and
compact type output are in the linked artifact and
`.scratch/ci-2a3b835-section3/`. Every receipt input hash was compared with
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


## Checked generic continuation

The generic library now has 270 locally checked declaration type/axiom
heads, up from the published 159. All 111 new complete types were reviewed;
only the three standard axioms occur. This is a component checkpoint, not
an additional numbered paper theorem. The actual ACVF library remains at
its previously checked 201 heads. Integration of the combined 471-head
scope is awaiting the new CI run.

The new modules prove full-base finite Boolean refinement, finite punctured
partition rigidity, intrinsic proper hole refinement and affine hole
closure, and preservation of a single positive region under atomic images.
All finite imaginary-code graphs retain every representative over the
original parameter base.

For corrected 3.11, FibreSupportFormulas proves joint canonical inverse-support
membership and uniform minimal support size. AtomicFiniteFibres obtains a
uniform bound on finite relation rows directly from source atomicity, with
no extra saturation or base-cardinality assumption. ProperInverseSupports
combines it with target atomicity, infinite disjoint target classes and
finite proper-ball non-covering to prove that inverse supports lie properly
inside the source ball. The actual ACVF connection remains to be compiled.

FiniteCofiniteClasses, QuotientCover, FiniteClosedHull and CoverRadiusFormulas
supply the remaining abstract trace, counting, intrinsic hull and full-code
radius constructions. Actual maximal-subball geometry, hull existence and
constancy are still needed for a complete 3.11 proof. The actual primitive
classification drafts for 3.6/3.8 are kept local until compiled; they are not
part of this publication.

The environment blocks the pinned Mathlib cache, so a bounded local source
build is preparing the complete actual-ACVF dependency import. The affected
generic proof batch has compiled locally before publication. CI will confirm
its integration with the unchanged actual library. HK is background for
proof ideas only; no HK citation or assumed result is introduced.
