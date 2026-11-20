# Review of the HK degree-zero convention

**Implementation status:** the accepted downstream correction and active Section 7 targets are now proved; see [the completion record](section%207/COMPLETION.md). The impact inventory below is the historical migration review, not a current list of unfinished tasks.

Reviewed November 15, 2026 (America/Los_Angeles), following the author's
instruction: “let's do it the HK way then.” The accepted target now retains
volume forms in **both measured degree-zero categories**, µRV[0] and µVF[0].
Ordinary RV[0], VF[0], and the unmeasured theory remain unchanged.

**The review is complete; correction is paused awaiting the upstream API.**
*(Historical, November 15, 2026. The upstream API was published and the
correction is complete; see the implementation status above. Noted
November 19, 2026.)*
The preserved staging work adds 18 modules / 112 exports under the corrected
convention, including degree-one geometric factorization, weighted zero
lift/classification and zero descent. See
[the current correction status](section%207/HK-CORRECTION-STATUS.md).
The earlier 1,802 modules / 5,798 exports retain their original types;
they are reusable proofs, not certificates for unmigrated new targets.
The review itself changed documentation only; the later checked correction
batch is recorded separately. The dependency pin is unchanged.
The author also explicitly included the special-transformations repository;
its current active Section 10 was reviewed separately, as detailed below.

The author will implement the predecessor changes in its own session.
[The standalone handoff](SPECIAL-TRANSFORMATIONS-HANDOFF.md) records that
session's scope and the interfaces needed by this repository. No predecessor
Lean implementation is being carried out in this session.

## Source and exact convention

[HK, arXiv:math/0510133v3](https://arxiv.org/pdf/math/0510133v3),
Definitions 8.10 and 8.13, retains the density in every measured degree.
Its Lemma 8.20(6) states generation by the unit-form point/cone pair.
[Yin, arXiv:1006.2467v1](https://arxiv.org/pdf/1006.2467v1),
Definitions 10.1 and 10.3, instead explicitly makes measured degree zero
ordinary. The sequel inherits those definitions in Section 2.
The author's new instruction adopts the former degree-zero convention;
it does not import any unproved HK theorem as a Lean input.

A degree-zero RV object must be a finite definable RV-labelled set D with
a definable nonzero density ρ. An isomorphism e must satisfy
ρ(d) = σ(e(d)) **as RV classes**, not just after taking valuation.
The empty-coordinate determinant is 1. There is no nonempty exceptional
set of dimension below zero. The same exact density condition is required
on measured VF[0]. The unit-density inclusion recovers the ordinary
degree-zero category. Multiplication multiplies densities, including
0×0, 0×positive, and positive×0.

This review concerns the project's nonzero RV-valued forms and finite-volume
categories. It does not enlarge the project to ambient RV[k,·], change the
parameter base, or adopt all of HK's other conventions.

## The special-transformations repository also needs correction

The current predecessor main is
`f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`, with an active 18-module
Section 10 library. Its `GradedCategories.lean` hardcodes ordinary zero
categories, and `ZeroDegree.lean` exports ordinary zero specializations of
10.4, 10.5 and 10.6. Those need actual weighted replacements/extensions,
including the Gamma-valued variants. Reuse `VolumeScale` for both weight
types and retain the existing positive category proofs. At zero the
RV-valued category preserves RV weights, while its Gamma-valued counterpart
preserves Gamma weights. The neutral-form subcategories recover ordinary
zero categories. No earlier section imports Section 10.

The sequel's pin `9cc9760892092dd34cfad4a6dee655843c52f30c` predates all
18 active Section 10 modules. Its Section 10 scaffolds are not the current
repository. Current main also changes earlier geometry relative to that
pin. Consume a checked compatible revision or backport the needed changes;
a wholesale switch to current main has not been validated. Positive
measured presentations in the two repos require explicit adapters.

The complete predecessor review and source-difference inventory are in the
separate checkout at `/workspace/special-transformations-hk/Section10/`:
`HK-CONVENTION-REVIEW.md` and `hk-impact-inventory.json`. The same correction
is recorded in that repo's working agreement and Section 10 status/handoff.
Its documented positive RV lift retains the finite-extension reference
premise; this review does not count that premise as discharged by the
sequel's separate field-theoretic work.

## Section-by-section findings

| Section | Required mathematical change | Material that remains reusable |
| --- | --- | --- |
| 1 | None; introduction only. Explain the changed measured convention when the final exposition is written. | No formal proof target. |
| 2 | Replace the vacuous degree-zero part of 2.34 by exact density preservation. Extend the measured lift/surjectivity interfaces corresponding to 2.35–2.36 to weighted degree zero. Update the interpretation of the notation in 2.37. | 2.15, language, finite-volume geometry, positive-degree descent, the Gauss graph and field-theoretic proofs. |
| 3 | No theorem statement or mathematical proof change identified. | All atomicity, ball and open-to-open results, with their existing scopes and corrections. |
| 4 | No theorem statement or mathematical proof change identified. | All preparation, cell and balanced-cell geometry, with the existing corrections. |
| 5 | No theorem statement or mathematical proof change identified. Its “volume map” means the finite-to-one coordinate map, not a measured density. | All completed RV[k] contractions and comparisons, including the explicit charts in 5.5. |
| 6 | No change to the unmeasured categories, kernel, integration or localization targets. Some Section 7 ports rebuild because their helpers share imports with measured geometry. | The original Section 6 library and the closed generated-base ordinary interfaces in Section 7. |
| 7 | Extend the measured foundations, mixed products, zero lift, full graded coefficients and zero-valued families; then re-establish all-degree assembly and complete the two raw obligations. | Positive-degree objects, Jacobians, elementary blowups and comparisons; most positive geometry through 7.10; generic groupification, grading, quotient and localization arguments. |

“No change identified” refers to this convention change. It does not remove
any pre-existing hypotheses, accepted corrections, or documented boundaries.
In particular, 3.17's existing distinction between its conditional statement
and ordinary-source existence is unaffected.

## Concrete interfaces that need changes

Paths below are relative to the repository root.

1. **Section 2's zero equations.**
   `section 2/IntegrationSection2/ConcreteVolumeMorphisms.lean` defines
   `IsVolumeIsomorphism` as `k = 0 ∨ (...)` and proves `zero_arity`
   without any weight condition. `VolumeDescentAllDegrees.lean` uses
   `PUnit` at zero and `True` for both preservation predicates. These
   cannot serve as the new measured interfaces. Retain `RVForm` at zero,
   require the pointwise density equation, and prove zero descent from
   the supplied lift and its empty-coordinate Jacobian. The positive
   theorem `corollary_2_34` is reusable. The pinned predecessor already
   supplies `hasMixedVFJacobianAt_zero_arity`; no dependency upgrade or
   new graph-field input is indicated.

2. **Measured objects and isomorphisms.**
   `section 7/Integration7/RVVolumeObjects.lean` and
   `VFVolumeObjects.lean` select ordinary objects at zero.
   `RVVolumeMorphisms.lean` and `AllDegreeVFVolumeClasses.lean` select
   ordinary isomorphisms there. Introduce density-bearing zero objects
   and exact weight-preserving isomorphisms on both sides. The positive
   structures and their Jacobian laws can be retained. Ordinary objects
   embed using density 1; they must not be silently identified with every
   weighted zero object.

3. **Places that currently discard a supplied form.**
   In `UniformVolumeData.lean`, `RVVolumeData.toObject` forgets its form
   at zero. `GradedVolumeProducts.lean` similarly makes `rvVolumeForm`
   constantly 1 and ignores the zero form in `rvVolumeOfForm`.
   Retain the given form in all three. Remove the zero-unit restriction
   from the corresponding density recovery lemma once the new definition
   actually makes recovery valid.

4. **Mixed product and blowup congruence proofs.**
   `ZeroFactorVolumeObjects.lean` and `ZeroFactorVFVolumeProducts.lean`
   currently pull back only the positive factor's form. Replace this by
   the product of both forms. Extend the matching `ZeroFactor*` map,
   isomorphism, swap, lift and class-product modules, including
   `ElementaryZeroVolumeProducts.lean` and
   `AllDegreeVolumeBlowupProducts.lean`. Positive×positive products are
   unchanged. The new mixed proofs must use arbitrary definable zero
   densities, not just a separately named constant rescaling.

5. **Zero lift, integration and all-degree quotients.**
   `GradedVolumeBlowups.lean` currently defines `MuIsp` at zero by ordinary
   isomorphism. Replace it with weighted isomorphism; positive blowup
   equivalence stays the same. Extend `ZeroVFVolumeClasses.lean`,
   `ZeroVolumeIntegration.lean`, `AllDegreeVolumeClasses.lean` and their
   additive/product assembly. Transport the density through the existing
   ordinary finite lift presentations to prove weighted zero lift
   surjectivity and injectivity. No elementary degree-zero blowup is
   required. Rebuild the all-degree lift and ring equivalences using this
   genuine weighted zero component.

6. **Degree-one factorization and the principal ideal.**
   `AdmissibleHeadVolumeFactors.lean` already proves finite fibres for
   dropping the last coordinate in every source degree. Its density-bearing
   factor is currently constructed only when the remaining degree is
   positive. Extend it to zero, keeping density `ω · f_last`. Then extend
   the point/cone factor isomorphisms in
   `ElementaryPrincipalVolumeFactors.lean` and the semiring argument in
   `PositiveElementaryBasicGeneration.lean` to degree-one sources.
   For a weighted zero point Z_c, the required identities are
   P_c = Z_c·P_1 and C_c = Z_c·C_1. General finite definable weighted
   families, not only named points, are required for the proof.
   Finally adapt `RawBoundaryKernelPresentation.lean`: show every remaining
   degree-one elementary difference belongs to the ideal generated by
   P_1−C_1. This is a proof obligation, not a consequence certified merely
   by changing a definition. Keep the stronger semiring congruence target
   separate from its groupified ideal consequence.

7. **Zero-degree function families and Jacobians.**
   `OrdinaryVFVolumeFamilies.lean` has no density field and its VF
   realization has unit form. Keep it for ordinary/unit-density inputs,
   and add a weighted zero family retaining a definable form on its mixed
   domain. Extend zero rows, parameter extension, AE equivalence, addition,
   coefficient actions and support restrictions. In
   `GradedAEVolumeFunctions.lean`, the full degree-zero component must use
   the weighted families. After pullback along φ, multiply their form by
   the actual inverse-Jacobian RV class, retaining finite labels and the
   original parameter base. Encode a density as an additional RV label
   where a presentation requires factorization through the RV projection.
   This supplies the missing raw degree-zero transform in 7.12.

8. **7.11, numbered 7.13, and normalization.**
   The current all-input raw 7.11 proof includes ordinary zero values;
   extend its zero-family argument to weighted values and reassemble
   supported Fubini. Positive raw 7.12 remains reusable. Numbered 7.13
   already has a proof for the actual kernel quotient; retarget its
   geometric inputs and zero component, retaining its grading algebra.
   Do not confuse it with the additional principal-ideal assertion just
   before it. The normalized coefficient ring, scalar extension, full
   function module and 7.14–7.15 must be instantiated with the new graded
   ring and extended zero families. Existing ordinary-input formulas only
   establish the unit-density subcase of the new targets. Do not assert
   that the old and new normalized rings coincide without a comparison
   proof.

9. **Boundary proofs and accepted scope.**
   `OrdinaryHeadFactorBoundary.lean` remains a valid statement about
   ordinary zero factors. `OrdinaryFibreDensityBoundary.lean` remains a
   valid obstruction to forgetting density. Neither obstructs the new
   weighted construction. Keep them labelled with their old scope.
   The accepted nonempty E hypothesis of 7.5 remains in force; changing
   coefficient degree zero does not prove the excluded empty-E case.

## A compatibility point to check during implementation

### Compatibility within the two repositories' existing scope

The author clarified that compatibility must be assessed within the scope
of the two papers. The earlier version of this review overextended the
checklist to HK's pure value-group and RES categories and tensor
decomposition. Those are not targets of either repository and are not
migration obligations. Adopting HK's measured-zero convention does not
adopt HK's entire theorem inventory.

**VF lifting.** The measured lift must pull back the supplied form in every
degree, including zero. On Grothendieck classes it must preserve addition,
products, the neutral element, and the weighted degree-zero scalar action.
Its kernel comparison must still use the actual measured blowup relation.
Keeping the old ordinary VF[0] would collapse all singleton RV weights
under the zero lift, whereas the new zero RV isomorphisms distinguish them.
That would break the claimed zero kernel description and all-degree
integration equivalence, independently of the factorization argument.
The existing `ZeroVFVolumeClasses`, `ZeroVolumeIntegration` and
`VolumeIntegrationSemiringEquivalence` interfaces therefore need replacement
zero branches, as well as the mixed-product proofs identified above.

**Gamma-valued forms already in scope.** Special-transformations Section 10
includes µ_Gamma RV and µ_Gamma VF, their measured categories, the forward
lift, surjectivity and additive class maps. Their zero branches must retain
Gamma weights and satisfy those existing statements. Preserve their actual
label maps, restrictions, neutral-form specializations and graded assembly.
This does not add a Gamma-valued version of every Section 7 theorem in the
sequel where that is not already an accepted target.

Where an existing construction passes from an RV-valued form to its Gamma
value, keep the valuation of the supplied form, including at zero, and
check its compatibility with the lift or product actually being used.
For example, RV point weight c gives Gamma point weight val(c), rather than
the neutral Gamma weight. A general new coarsening-functor package, its
all-degree commuting-square theorem and a definable inverse are not extra
completion requirements. No definable choice of RV representatives of
Gamma weights is assumed.

**Gamma parameters are a different interface.** In the sequel,
`Section6.FiniteRV.GammaObjectAt` describes an RV object with parameter
definability certificates, and `Section7.GammaVolumeObjects` describes an
RV-valued positive object with such certificates. Neither is HK's µGamma
category. Preserve these original-base definability certificates when
adapting the measured interfaces; their presence does not call for creating
pure Gamma or RES categories.

The active compatibility work is therefore the existing measured RV/VF
categories and lifts in both repositories, the Gamma-valued counterparts
already targeted in the predecessor, and the actual coefficient, function,
quotient and normalization maps used in the sequel. These new weighted
compatibilities have not yet been proved in Lean.

### Point localization

Exact RV weights at zero retain distinctions that a positive-degree point
can forget through its lower-dimensional RV exception. Consequently,
multiplication by the positive point class must not be assumed injective.
The localization machinery was deliberately built without such an
assumption and is reusable. Any claim comparing zero coefficients before
and after point normalization needs its own proof. This is an interface
check, not a new counterexample to HK's theorem.

## Dependency inventory and verification scope

The source review covered all **3,431 local library modules**, including
entry points, under the eight registered numbered-section libraries.
Nested comments and strings were masked before extracting local imports
and selected measured identifiers. The four foundation roots were
`IntegrationSection2.ConcreteVolumeMorphisms`,
`IntegrationSection2.VolumeDescentAllDegrees`,
`Integration7.RVVolumeObjects`, and `Integration7.VFVolumeObjects`.

| Section | Local modules | Reverse import exposure to these roots | Modules mentioning selected measured interfaces |
| --- | ---: | ---: | ---: |
| 2 | 37 | 5 | 8 |
| 3 | 364 | 0 | 0 |
| 4 | 96 | 0 | 0 |
| 5 | 395 | 0 | 0 |
| 6 | 736 | 0 | 0 |
| 7 | 1,803 | 1,549 | 784 |

The 1,549 figure is a conservative **rebuild dependency closure**, not a
count of proofs requiring mathematical rewrites. For example, all 82
`ClosedSection6*` ports lie in it through shared native-domain helpers,
but none mentions the selected measured interfaces directly. Their targets
are ordinary. Likewise, lexical reference counts are navigation aids,
not a semantic classification of every declaration.

The complete exposed-module and measured-reference lists are saved in
[`section 7/review/hk-impact-inventory.json`](section%207/review/hk-impact-inventory.json).
Its source identity for each section hashes sorted lines
`module_name source_sha256\n`, preserving the reviewed Lean snapshot without
duplicating the existing full verification receipts. Pinned dependencies
are outside this local graph; their relevant Jacobian interfaces and
Section 9 status were read separately. At the sequel's old pin, Section 10
contains only legacy scaffolds. The current predecessor does have an active
measured library; its separate review above is necessary before planning
a dependency update.

No fresh compilation or type/axiom audit is claimed for this documentation
review. During implementation, check new foundations and affected consumers
once per coherent proof batch, then perform the final integrated check.
Retain the existing audits for unchanged proofs.

## Implementation order

Build weighted zero objects and their exact isomorphisms in the predecessor
first, then its zero lift and the sequel's mixed products through compatible
adapters. Establish the degree-one point/cone factorization
before migrating the entire function stack; it gives a small concrete
validation of the new scalar action. Next extend weighted zero families
and raw 7.12, followed by full 7.11 and the graded/ring/normalized assembly.
Preserve positive proof APIs through adapters or a staged namespace while
changing their all-degree consumers. Update registries and completion
claims only when those actual new theorem types have been checked.
