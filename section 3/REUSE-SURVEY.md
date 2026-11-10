# Section 3 reuse survey

Reviewed November 10, 2026 (UTC). Source: arXiv:0809.0473v2, Section 3
through Proposition 3.24. No OpenMathOS source or proof claim was imported.

## Fixed inputs

| Input | Revision / terms |
| --- | --- |
| Special transformations | `9cc9760892092dd34cfad4a6dee655843c52f30c`; MIT |
| Inherited ACVF-QE | `939346b0a99899e22a873479364e3cc5d142731c`; MIT |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679`; Apache-2.0 |
| Lean | `leanprover/lean4:v4.35.0` |

Read the predecessor's LANGUAGE-ERRATA.md and relevant section status before
reuse. The corrected common LRV has named RV inversion, one absorbing RV
element, and the paper's Gamma order reverses Mathlib's valuation order.
Dependency pins do not discharge open mathematical inputs in legacy modules.
No new external dependency or toolchain upgrade was introduced. The user's
citation policy allows already formalized results; unformalized results
outside the approved list require approval. The Johnson result below is an
existing proved Lean theorem in the pinned dependency.

## Reused sources and proved bridges

| Source | Decision and sequel bridge |
| --- | --- |
| Mathlib `ModelTheory/Definability.lean` | Use actual `Set.Definable`, definable maps, Boolean operations and quantifier/projection closure. Definition 3.1 is defined over these first-order predicates. |
| Mathlib `Order/BooleanSubalgebra.lean` | Reuse Boolean closure induction for finite ball support. Support witnesses do not replace the ACVF language. |
| Predecessor `Section3/GammaBaseTools.lean` | Adapt `promote_definable_tuple_fibre`'s formula-relabeling construction. `ImaginaryParameters` proves finite-support full-preimage bases and exact parameter promotion. |
| `Parameters`, `SortedBoolean`, `CMinimal`, `RVUnaryLift`, `GammaThresholdGeometry` | Reuse normalized raw/sorted bridges and proved C-minimality. `Geometry.lean` keeps the stronger single-ball valuation conversion and actual laminar geometry. |
| `ClosedBallCodes`, `ClosedBallQuotient`, `OpenBallCodes`, `GeneralBallCenters`, `GeneralCosetChoice` | Keep the existing quotients by equality of underlying balls. `BallPresentation` supplies full surjective real codes, membership and interpreted equality; `ParameterPresentation` combines actual Gamma and ball names. No centre or radius representative is named. |
| `Section4/GammaPredicates`, `GammaControllerDefinability`, `GammaOrderControllers`, `GammaFiniteDefinablePoints`, `GammaDefinableClosure`, `FiniteOrderSamples` | `FullGammaSyntax` and `FullGammaPoint` adapt these proofs to the combined base. Real-code specialization obtains a finite controller; its intrinsic minimality recovers definability over the original base. Finite ordered points, multiplication, inverses and unique square roots yield the required definable samples. |
| `Section3/DefinableCosets.lean` and Mathlib `QuotientAddGroup` | Use the actual additive quotient and its full difference relation. The interpreted range-family construction derives definability by real universal/existential quantifiers, including arbitrary original imaginary names. |
| Mathlib `Valuation.leAddSubgroup`, `ltAddSubgroup`; predecessor RV normalization/value APIs | `NamedRadiusAtomicity`, `GammaRadiusAtomicity` and `FullGammaRadius` prove the zero-centred subgroup and all translated ball equalities. A Gamma radius is represented by its whole value fibre, not a selected RV lift. |
| `Section3/AdditiveCosets.lemma_3_18_1`, `BallFibreConstancy` | `FullCosetExceptions` specializes the complete graph and subgroup only to prove finiteness, then retains the original-base statement. Powerset-valued functions are full relations in every finite RV arity. |
| Mathlib valuation/quotient APIs; predecessor `Average.le_one_natCast`, `Average.nat_unit` | `InfiniteCosets` proves the integer-translate injection into distinct smaller-ball cosets. `GammaCosetGeometry` derives its unit premise from ACVF(0,0) and proves the actual Gamma/valuation membership and intermediate-radius bridges. |
| Mathlib `Order/Preorder/Finite.lean` | `PuncturedDecomposition` uses finite extrema to replace all proper support balls by maximal disjoint holes. The result is a finite disjoint decomposition, without original-base component definability or primitive classification. |

The inherited source and notices remain in the dependencies. The generic
core is independent of ACVF. Actual wrappers freeze original-model data
before introducing canonical normalization for first-order definability.

## Current mathematical consequences

- `AdjoinBall.lemma_3_2`: arbitrary genuine real/Gamma/ball base, with the
  input-ball name adjoined in the conclusion and nonalgebraicity of the output.
- `FullGammaAtomicity.lemma_3_3`: every finite Gamma tuple, every finite real
  output arity, full combined base. The original-base definable nontrivial
  value and ACVF(0,0) remain explicit.
- `FullGammaRadius.lemma_3_4`: full combined base, original-base definable
  ordinary Gamma radii, singleton and VF cases. Ambient complete types need
  not be definable.
- `OpenBallConstancy.lemma_3_9_open` and `corollary_3_10_open`: complete graphs
  on the stated domains, all finite RV output arities, exact sequel open-ball
  predicate and combined base. The corollary can first adjoin an unnamed
  subball radius using 3.3. No finite-exception, infinite-class or constancy
  conclusion is left as an assumed model field.
- `PaperBalls` encodes Definition 3.5; `PuncturedGeometry` proves the initial
  finite decomposition step of 3.6. The primitive classification is open.

The domain wrappers extend a function by the empty set only inside the proof.
The whole-field open-ball case is vacuous under atomicity, because the
parameter-free singleton zero separates VF from one. The predecessor's
explicit singleton-open convention is not used as the sequel's predicate.

## Verification and next reuse boundary

The full root build, inherited foundation audit, both Section 2 audits and
360 Section 3 audits passed in [CI run 42845510919](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42845510919)
at source `2a3b835c341e28f1662441bb84c1f8cda89b5fbe`. All five newly exported
types since the 355-declaration checkpoint were reviewed, together with
the actual ball family and original-model/normalized definitions. Every
receipt input hash matched the committed source. Only propext,
Classical.choice and Quot.sound occur. The receipts distinguish exact
compiler/source identities and incremental builds.

`MinimalBallSupport.lean` proves minimal finite support uniqueness in a
laminar family with the explicit non-covering property.
`CanonicalBallSupport.lean` supplies that property from the existing Lean
proof `ValOneEC.Johnson.ne_finite_union_of_proper_subballs` (Johnson Lemma
2.3.7) in pinned ACVF-QE `Proofs/JohnsonGeometry.lean`. It supplies IsAlgClosed
VF and derives a nontrivial valuation witness from an actual Gamma value
greater than one. The extra raw-universe top is absent from minimal supports.
No unformalized external theorem is cited for this bridge.

`SupportFormulas.lean` defines fixed-length support codes and their full
interpreted family over the original base. Minimal-support uniqueness
identifies its range with the canonical support without naming a chosen
tuple. `BallCodeGeometry.lean` proves both directions of encoded-ball and
actual-quotient coverage from the pinned chart bodies; the raw chart
argument follows `GeometryBridge.isKBall_vfImage`, retaining a single ball.
`CanonicalSupportFamily.lean` combines these steps to obtain the finite
original-base definable support family. These are now fully checked.

`MinimalBallSupport.support_covers` and
`PuncturedDecomposition.finite_decomposition_of_support` keep the canonical
parent family fixed while deriving its disjoint positive regions.
`RegionFormulas.lean` proves full-code strict containment, region membership
and positive-parent definability; `CanonicalRegions.lean` supplies the actual
finite original-base family and its disjoint decomposition. `HoleFormulas.lean`
and `CanonicalHoles.lean` identify maximal proper support balls intrinsically
and prove the joint hole/parent relation definable over that same base. All
of these steps are now checked by the full build and audit above.

`CodeEquality.lean` proves intrinsic equality and code-image definability;
`BallKindPredicates.lean` uses it for full original-base open/closed tests.
`AtomicCanonicalRegions.lean` proves uniform puncture status and the generic
uniform-property step on canonical positive regions. Radius comparisons in
ValuationRadius.lean are supplied with actual ACVF density in
BallRadiusGeometry.lean using the pinned formalized
`ValOneEC.Johnson.exists_val_between'`; nontriviality is derived from `δ > 1`.
PaperBallInvariants.lean proves radius existence and uniqueness, including
the singleton and VF conventions. ValuativeCentreGeometry.lean reuses the
pinned predecessor's `Balls.openDisc_value_constant` and
`closedDisc_value_constant` for centre existence, and proves uniqueness on
nonempty VF sets. Their full types and standard axioms are checked.

`OrdinaryCentreFibres.lean` reuses the pinned
`GammaParameters.same_scalar_normalize` and `same_scalar_definable` and
the checked normalized RV-map argument. Its entire ordinary centre graph,
finite original-base Gamma image, individual occurring values and parent
tests are checked. `UniformValuativeCentre.lean` combines these tests with
canonical region atomicity and actual centre uniqueness to obtain a common
valuative centre, including infinity and an empty positive family. All code
fibres are retained and the base is unchanged. The new generic free-real-
output image-code formula is also checked.

Next come the invariant radius graph, finite image and common radius, then
primitive hole classification. ClassCoverage.lean proves the logical whole-fibre coverage step.
SameRadiusCoverage.lean now proves Corollary 3.7 from the checked
FullGammaAtomicity.lemma_3_3_one_unary, FullGammaRadius.gamma_subgroup
and FullBallCoset.cosetRelation_definable. The input radius is temporarily
adjoined using 3.3; all new types and standard axioms passed. The open/closed
wrappers include VF and singleton cases. The proof does not use open 3.6. Later
image/open-to-open results remain open. No result is counted by assuming
its missing geometry.


## Checked generic support and hull continuation

The dependency pins and licenses above are unchanged. The generic library
now contains 270 locally compiled and type/axiom-audited heads. All new
complete types were manually inspected. No HK citation or assumed result
is introduced; the user permits only background proof ideas from HK.

The continuation uses existing interpreted-code quantifiers and ordinary
first-order counting. Source complete-type atomicity makes the finite row
bound uniform without saturation. Minimal ball support, laminarity and
finite proper-subball non-covering give proper inverse supports. Mathlib's
valuation and additive quotient APIs support the affine transport and
closed-hull geometry; density and natural-number valuation-unit inputs stay
explicit for the later actual ACVF wrappers. No new external theorem input
or dependency is assumed. These components do not establish the open
numbered primitive-classification or separation statements on their own.


## Primitive classification and images, local 551-head checkpoint

Pins and licenses are unchanged. OrdinaryRadiusFibres and UniformRadius now
check the complete actual radius graph and its constancy. BallEnlargementGeometry
uses actual compatible valuations and the already checked Gamma density and
radius comparisons. Its same-radius re-centring is proved by the ultrametric
inequality; it does not import the predecessor's legacy RV conventions.
NamedClosedHoleCut uses the checked original-base radius samples and intrinsic
finite hole refinement. AffineArithmetic uses the pinned RingSyntax sorted-term
interpretation with natural numbers in syntax, not as new parameters. The actual
affine quotient argument supplies all hypotheses of the checked generic closure
and full-code refinement. PrimitiveDecomposition proves3.6 from those facts.

PuncturedImageComponents applies the checked finite punctured partition theorem
and exact minimal-support recognition, proving source-parent definability rather
than assuming it. PrimitiveImages then proves3.8. All59 new actual complete
exported types match their individually compiled and manually reviewed audits
exactly; the full551-head audit and root/foundation/Section 2 checks pass locally.
No new external citation, unproved HK result or dependency pin is introduced.


## Corrected separation and open images, local 600-head checkpoint

No pins, licenses or external theorem inputs changed. The49 new actual heads
supply the original-base inverse-support graph, intrinsic span radius, actual
minimal native closed hulls, constancy across target classes, finite/cofinite
closed-cut traces over an enlarged base and the assembled separation contradiction.
Nonemptiness of R is explicit; both projections are proved onto. No saturation
is assumed for finite-row uniformity or the geometric contradiction. The
unnamed target radius is temporarily adjoined using checked3.3. Actual3.12
and 3.13 then follow from separation and the checked3.8 image classification.
All49 complete types match their separately compiled and manually reviewed
snapshots exactly; the full local root and 600-declaration audit pass.


## Closed-image obstruction3.14, local 630-head checkpoint

Pins and licenses are unchanged. The finite-arity polynomial support proof
is extended from pinned MIT Section3.PolynomialSupport, with source attribution
in its header; the existing Section4.MultivariateSyntax interpretation is
imported. Other syntax reuse includes the proved original-base QF theorem,
PolynomialZero.zeroSet_parameterField_definable, sorted coefficient-name
elimination, and the exact ring-term and parameter-field APIs already surveyed.

The new bridges prove all-code elimination of the one source ball name,
Gamma-only finite specialization without VF-field enlargement, a two-VF QF
presentation over that field, nonzero specialization on the atomic source,
and a zero-free product via corrected 3.11. ClosedBallRoots.enlarge and
polynomial_rv_constant_openDisc supply the checked native closed-ball escape.
Every model/characteristic/nontriviality hypothesis is supplied explicitly;
no HK citation, unproved polynomial-presentation premise, saturation premise
or new chosen field parameter is used. Full local root and 630 audits pass;
all 30 new complete types exactly match reviewed individual snapshots.

## RV difference maps and integer equivariance toward 3.16

Dependency pins and licenses are unchanged. The exact checked declarations
`Balls.rv_sub_constant_openDisc`, `Balls.rvFibre_eq_openDisc`,
`CanonicalRV.encoded_eq_iff_close`, native ball laminarity and the existing
compatible-valuation and Gamma-representative APIs supply the geometry.
The new subball-image theorem derives its conclusion from this sequel's
checked 3.3, named-radius 3.4 and 3.13; its definable atomic ambient-set
hypothesis is explicit. It is not the unrestricted 3.15 statement.

Full interpreted-base formulas retain both input/output difference values,
all original imaginary codes and the exact graph on the source domain.
The normalized difference term is proved equal to the original RV of a
VF difference. Checked 3.9 makes its RV-pair family independent of the
source point. Subball images prove single-valuedness; the transposed
partial inverse graph and the checked atomic open image prove injectivity
of that relation. Mathlib's proved `Function.invFunOn` API supplies the
partial inverse; no inverse definability is assumed.

The integer step uses a new native valuation estimate for sums of strictly
small errors, the previously checked characteristic-zero valuation of
nonzero natural numbers, and preservation of open balls under integer
affine combinations. It proves actual integer equivariance of the common
RV relation. All full-base, ACVF00 and original-base nontrivial Gamma
hypotheses remain explicit. No saturation, HK citation or unproved
linearity premise is introduced. Descent of the slope to Gamma and the
remaining constant-slope argument are still open.

The full root and 658 local audits pass; all 28 new complete types match
reviewed individual snapshots, and the 630 earlier types are unchanged.

## Gamma slope fibres and order, local 679-head checkpoint

Pins and licenses are unchanged. The exact checked
`AdditiveBalls.affine_rv_injective` supplies injective nonzero-natural orbits
inside one actual RV value fibre. The exact checked
`rv_value_fibre_finite_or_cofinite` applies after finite real-code
specialization and naming a coefficient only within the proof. Infinite
orbits and coefficient uniqueness prove value-fibre constancy.

The original-base full-code Gamma graph is proved definable, including every
nonzero RV representative of each Gamma input. The checked
`GammaRVFamily.finite_projection` supplies finite image with genuine
`Saturated M kappa`, `aleph0 <= kappa` and `mk B.real < kappa` hypotheses
explicit. Finite imaginary-code support preserves that smallness bound.
No saturation premise is introduced into the separate value-fibre constancy
or strict valuation-order theorems. The latter follow from proved open
subball images and a new native ultrametric separation bound. All 21 new
full types match reviewed individual snapshots; all 658 prior types are
unchanged in the successful full root and 679-declaration local audit.

## Assembled Gamma-linearity 3.16, local 707-head checkpoint

Pins and licenses are unchanged. The exact formalized Mathlib APIs for
continuity of order isomorphisms, continuous group division, finite closed
sets in T1 spaces and locally constant fibres were inspected before use.
The pinned finite-order-controller theorems and their exact hypotheses
were inspected as well. New proofs supply the finite-image continuity
bridge, removal of locally redundant controller endpoints, constant shift
on the actual Gamma tail and its endpoint ratio. No completeness or
Archimedean assumption is used.

Actual ACVF bridges supply domain realization, the coefficient/output-value
formula, the strictly increasing Gamma map, surjectivity and its full
order isomorphism. Fixed-output Gamma rows retain the full original-base
graph and obtain finite controllers only after finite-code specialization.
The final 3.16 theorem uses actual field difference values and actual radius
invariants; every prerequisite is supplied by checked proofs. Genuine
saturation and smallness from the finite projection theorem stay explicit.
The full root and 707 local audits pass; all 679 previous full types are
unchanged and all 28 new ones exactly match reviewed individual snapshots.
No new external citation or unproved HK input is used.

## Nonalgebraic ball choice and Corollary 3.17

Pins and licenses are unchanged. The exact already formalized declarations
`Section4.NonalgebraicTypes.realize_unary_definable_fip`,
`Section3.NormalizationSaturation.Saturated.normalize`,
`Section4.gammaDcl_of_named_code` and `Section3.small_union_finite` were
inspected before reuse. These provide real saturation, its reduct transfer,
named-code Gamma definability and preservation of smallness under finitely
many temporary real parameters. No saturation of ball imaginaries is assumed.

New proofs construct a nonalgebraic member of an infinite disjoint definable
ball family, provide the actual interpreted identity graph and apply 3.2.
The fixed-radius subball family is proved infinite using the checked actual
Gamma-coset geometry and finite-cover theorem. Full-code map specialization
happens only inside the proof, so arbitrary original Gamma/ball names remain
permitted. Applying 3.16 gives the actual local Gamma-linearity statement and
then the paper's least-threshold exclusion, including VF source. Existence
of a least-radius function is not asserted by its definition. All 21 new
full types match individually reviewed audits and all 707 previous types
are unchanged. No new external citation or unproved HK input is used.
