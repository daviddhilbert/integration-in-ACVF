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
