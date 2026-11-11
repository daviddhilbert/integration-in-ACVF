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
  finite decomposition step of 3.6. The primitive classification is now checked; see STATUS.md for the subsequent proof chain.

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

## Actual RV-fibre and coefficient-tail components

Pins and licenses are unchanged. New proofs reuse the already checked
actual Gamma-coset family, native RV closeness, residue-characteristic-zero
integer orbit and finite-cover argument to construct atomic RV fibres.
They reuse genuine real FIP saturation and normalization transfer; no
quotient saturation is postulated. Full-code coefficient rows specialize
one RV parameter only inside their controller proof. Finite controller
endpoints and the checked finite projection give actual eventual RV
coefficient constancy without completeness or Archimedean assumptions.

The pinned RingSyntax, term normalization and Mathlib definable-term APIs
were inspected before representing the actual affine error. The partial
function graph retains the original imaginary base, with its real affine
constants explicitly named. Checked 3.9 supplies actual RV error constancy;
native valuation estimates recover the affine RV difference under the
stated strict error bound. All 23 new full types match reviewed individual
audits and all 728 earlier types are unchanged in the fresh 751-head audit.
Full 3.18 is not counted. PROOF-OBLIGATIONS.md records the additional
left-endpoint argument still needed. No new external citation or unproved
HK input is used.

## Finite-fibre means and the replacement proof of 3.18

Pins and licenses are unchanged. Full types and hypotheses of the pinned
`VFExchange`, `VFAlgebraicity`, `Barycentre`, `FibreEnumerations`,
`FiniteFibreMeans`, `RawClosure.finite_of_definable_subset_algebraic`,
`NormalizationSaturation` and finite-parameter cardinal lemmas were inspected.
Mathlib's field algebraicity matroid supplies exchange after proving the
parameter-field identity for arbitrary real bases. The two substantial MIT
proof adaptations preserve source attribution in their headers.

New full-base enumeration and mean graphs quantify all enumerations and
retain unchanged imaginary parameters. Atomic image completeness supplies
the finite bound. RV mean-centred nonconstancy plus checked 3.9 proves the
constant-or-injective error-map theorem, with its real-definable larger
domain and genuine saturation/smallness explicit.

The final proof specializes only finite original graph support and finite
real constants inside the argument. Checked real saturation and 3.2 choose
a new atomic RV fibre after this enlargement. Original 3.16 supplies the
Gamma scale; applying it again to the proved injective error map gives the
contradictory image radius. The original whole source is never assumed
atomic after naming its centre, slope lift and image of centre. Every final
hypothesis and actual RV equation was inspected; no endpoint assertion or
unproved external result remains as an input. All 43 new complete types
match reviewed individual audits, and all 751 earlier types are unchanged.

## Unnamed-radius open-ball atomicity over real/Gamma bases

Pins and licenses are unchanged. Full types and source of the already
formalized `MixedRootFree.mixed_qf_rootFree_constant`,
`PolynomialObstacles.obstacles_definable`, `OpenBallCodes.ball_eq_open`,
normalization and polynomial RV factorization APIs were inspected.
`CompleteTypeRVProfiles` adapts the pinned MIT root-free proof with explicit
attribution and uses checked Gamma specialization without changing the
original VF coefficient field. No new citation is introduced.

The self-centred profile quantifies all native radius codes and proves
agreement with the actual ball imaginary. It leaves one VF variable and
one RV radius variable, so a finite original-base polynomial obstacle set
works uniformly. Completeness and infinitude exclude those obstacles even
when the ambient set is not definable. This yields unnamed-radius open-ball
3.4 and then 3.15 over real/Gamma bases, with no saturation or originally
named radius. Old ball parameters remain excluded, explicitly and honestly.
All 11 new complete types match individual reviewed audits and all 794
earlier types are unchanged in the fresh full 805-head local check.

## Pure-field definable Dedekind finiteness and cofinite conservation

Pins and licenses are unchanged. Exact source, full types and hypotheses
of Mathlib `FiniteField.frobeniusAlgEquivOfAlgebraic`, finite-field root
polynomials, splitting/range lemmas, definability invariance, finite-adjoin
finiteness, ACF completeness and characteristic-zero transfer were inspected.
The construction adapts Mathlib's Apache-2.0 `FieldTheory/AxGrothendieck.lean`
with attribution. Its existing polynomial-map theorem is not treated as
a theorem about arbitrary definable maps: the latter is proved here.

Frobenius invariance supplies the new finite-subfield preservation step.
A first-order partial-injection relation sentence is defined and its full
semantics proved. Algebraic closures of finite fields satisfy it by a finite
restriction argument. Checked completeness and characteristic transfer
then prove the result in all algebraically closed fields. Finite patching
and an actual definable inverse prove finite-complement conservation.

All 19 new full exported types match their individually compiled and
manually reviewed snapshots; all 805 prior full types are unchanged in
the fresh full 824-head local audit. All use only the permitted standard
axioms. These are supporting pure-field results, not a completed 3.22.
No unproved conservation or external citation is introduced.

## Native residue coordinates and finite tagged-line conservation

Pins and licenses are unchanged. Inspected exact Mathlib valuation-subring,
residue-surjection, residue-zero and maximal-ideal types, and the pinned
predecessor's `CanonicalResidue.residue_eq_iff`, residue normalization and
native `ModelResidue` interpretation. The canonical hypothesis in residue
purity is retained explicitly in the new graph bridge. No outside citation
or unproved residue conservation result is used.

Thirty-one new complete types and all twelve new graph/coordinate definitions
match their individually compiled and manually reviewed snapshots in the
fresh full 855-head local audit. All 824 prior full types are unchanged;
all 223 source hashes match; only the three permitted standard axioms occur.
The new pure-field conservation proof applies to actual tagged-line graphs.
The independent valuation geometry identifies actual maximal open classes
and finite holes with actual residue coordinates. The induced definable
quotient-map assembly remains a separate obligation for full 3.22.

## Full affine residue graph and intrinsic maximal classes

Pins unchanged. The pinned totalization's exact IsCanonical definition,
Structure.ext, residue reduction formula and actual valuation comparison
types were inspected. CanonicalModelEquality proves equality of the whole
canonical interpretation with its normalization, without identifying
quotients of different structures. Actual VF division is eliminated by
an existential variable and the checked normalized field-error ring term.

All16 new full types and8 new definitions were checked against individually
compiled and reviewed snapshots; one display has only two reviewed
existential-notation changes. All16 combined-context types match exactly in the fresh full871-head audit; all855 previous types
are unchanged and230source hashes match. Standard axioms only. Finite
proper-subball non-covering is the already formalized pinned theorem,
not an unproved outside citation. Open-to-open kernel preservation and
the exact existential graph of the induced quotient are proved, with
finite-family coordinate assembly still a separate obligation.

## Complete 3.22 and general-model transport

Pins and licenses unchanged. Exact predecessor ball-set normalization,
Gamma code and definability specialization types were inspected. All43
new full types and coordinate definitions, including Chart fields, were
reviewed. Explicit original versus normalized arguments in openness,
nontrivial Gamma and finite-hole sums are distinct; compact display does
not identify their interpretations. All871 prior types unchanged,43new
types exactly match individual reviewed snapshots,244hashes match in the
fresh914-head local audit; only standard axioms. Every quotient, graph,
conservation and normalization bridge for full3.22 is proved.

## Proposition3.23 from checked atomic maps and actual hole counts

Pins unchanged. Reused exact full types of arbitrary-radius
OpenSubballImages.image_open_of_atomic, actual inverse graph and
SeparationFunctions.no_finite_to_one_to_open. No unrestricted3.15 or new
outside citation is assumed. The definable atomic ambient hypothesis is
explicit. All12 new full types and both shape/component definitions are
reviewed; all914 prior types unchanged and248source hashes match the
fresh926-head root/type/axiom audit. Only permitted standard axioms.
All six distinct ordered shape pairs and singleton/VF edge cases are checked.

## Real-base3.19: both compactness steps and actual finite refinement

Pins unchanged. Read the predecessor Section5 and Section9 statuses and
searched their preparation/Jacobian exports; their scopes do not directly
provide the required full interpreted-base open-to-open partition. No such
conditional result is imported. Instead reuse exact checked
Section3.TupleCompactness.raw_definable_formula_tuple,
Saturated.definable_finite_subcover,andSaturated.normalize,from the pinned
MIT predecessor. The new finite-tuple FIP proof and type-neighborhood
argument use genuine saturation. Original-base bad configuration syntax
uses the existing full ball presentation and open-kind chart equivalence.
The actual inverse and finite Boolean refinement reuse checked project
declarations. All17 new full types and definitions are reviewed; all926
earlier full types unchanged in the successful943-head combined audit.
Real-base3.19 retains its explicit empty imaginary base; no full-scope
completion is claimed. No new outside citation or HK input.

## Full original-base open3.4/3.15 and3.19

Pins unchanged. Exact checked predecessor inputs are real/Gamma root-free
profiles and open-ball atomicity,the genuine normalization/saturation and
finite-subcover interfaces,and small finite real parameter extension.
Mathlib.Order.Preorder.Finite.exists_maximalFor is reused after exact type
inspection for finite membership profiles. Project inputs include actual
C-minimal finite support,finite proper-subball non-covering,full interpreted
range syntax and atomic_below_complete_type(with no nonalgebraicity premise).
No unproved theorem from predecessor Sections5/9 is imported.

Finite hitting points for splitting-open-ball families are constructed via
internal finite real codes and finite covers. Complete types remain over
their actual base. Intrinsic terminal classes eliminate those auxiliary
points from the final atomicity proof. This is an independent replacement,
not the referee report's proposed QE argument. Full3.19 then follows the
paper's compactness proof using common real presentations only internally;
finite original formula support removes any bound on all imaginary names.
All26 new full types are manually reviewed and exactly match the combined
969-head audit; all943 published types unchanged,all270 source hashes match.
Only permitted standard axioms. No new outside citation or HK input.

## Full3.4 including unnamed closed radii

Pins unchanged. Exact source/type inspected for pinned
Section3.MixedRootFree.mixed_qf_rootFree_constant_closed:actual coefficient
field,well-sorted QF formula,closed-disc root avoidance,and finite RV tuple
scope. Every premise is proved by the new closed profile consumer.
The actual closed ball chart and non-strict valuation bounds give the
self-centred quotient bridge. Real/Gamma atomicity covers all ball kinds;
the conditional real cover helper's atomicity premise is supplied,not
retained in the final original-base theorem. The intrinsic finite-hitting
argument is reused unchanged. All969 previous complete types unchanged,
all14 new full types exactly match individually reviewed audits,and all277
source hashes match the successful983-head local root/type/axiom audit.
Only permitted standard axioms. No referee claim,new outside citation or
HK result is a proof input.

## Coordinate fibres and invariant real-label promotion

Pins unchanged. Inspected the exact full type and source of
SpecialTransformations.ModelTheory.promote_definable_tuple_fibre in pinned
Section3/GammaBaseTools. It promotes raw real constants to free variables;
it does not by itself preserve invariance of finite imaginary codes at all
new labels. CodeSupportHull proves that missing invariant extension using
universal valid-code representatives. The finite tuple presentation itself
is proved definable. RealParameterPromotion proves exact specialization and
full original-base definability. No chosen representative is a final name.
PointwiseCoordinatePartitions uses the project's checked full3.19; source
and target context labels are the only added real names. Whole-map injection
proves scalar fibre injection. The1004-head full local audit preserves all983
old full types, matches all21 individual reviewed new types and287 source
hashes, and uses only permitted axioms. Uniform global3.21 remains open.

## Full uniform coordinate partitions3.21

Pins unchanged. Reused the checked genuine tuple finite-subcover theorem
in pinned Section3/TupleCompactness after inspecting its exact source/type;
finite index reindexing and inverse pullbacks are proved. Existing project
Boolean refinement is extended to simultaneous finite cover refinement,
including an empty family. All open-image tests quantify actual ball codes;
forward and swapped restricted graphs give exactly actual OpenToOpen.
No external citation,HK input or referee claim is used. Full3.19,real-label
promotion,and valid-template definability supply every local premise.
The1042-head full root/type/axiom audit preserves all1004 prior full types,
exactly matches38 individually reviewed new full types,and302 source hashes.
Final3.21 has no finite original imaginary or local-choice hypothesis.

## Independent3.24 boundary check and Gamma bounds

Pins unchanged. Reused the actual proper gamma-ball geometry,full ball-code
membership syntax,real-parameter specialization,and named Gamma singleton
theorem after reviewing their full types. The counterexample uses actual
Definition2.2 predicates and actual OpenToOpen,not a surrogate relation.
It is nonempty and retains an original nontrivial Gamma name.
Finite endpoint controllers,finite extrema and order-pattern preservation
supply actual LUB/GLB and a finite/interval dichotomy. No unproved Euler or
monotonicity result is cited. FullGammaBounds supplies each controller
premise from the already checked full-base ACVF00 theorem.
All1042 old types are unchanged;9 new types match individual reviewed
audits,and305 source hashes match the1051-head full local audit.
The author has now explicitly approved the ordinary closed-parent correction.

## Actual radial RV quotient and Gamma matching toward3.24

Pins unchanged. Exact source/full types reviewed for actual open-ball RV
constancy,gammaBall/RV-fibre equality,open/closed recentering,intrinsic
maximality under OpenToOpen,and the generic surjective-coordinate factor.
Pinned GammaRVSeparation.finite_image_of_definable_cuts is applied only after
constructing its entire guarded cut graph and proving genuine small-base
saturation hypotheses. Actual infinite_gamma_fibre and finite/cofinite
traces supply all dominant-row inputs. The actual definable inverse supplies
every target match; generic matching then proves true surjectivity.
No Ax/HK/Euler citation is introduced. The final Gamma graph is not yet
proved first-order definable. All49 new complete types match individual
reviewed audits,all1051 old types are unchanged,and318 source hashes match
the full1100-head local root/type/axiom audit.

## Definable matching graph and interval reduction

Pins unchanged. Inspected the exact checked raw uniform_finite_side and
finite injection/cardinality declarations. The full original graph has
finite imaginary support internally; common finite real presentation gives
genuine small-base saturation. Distinct RV witnesses express the exact
cofinite matching graph on all proper value codes. No old-imaginary bound,
choice assumption or external citation is introduced. All30 new full
types match individual reviewed audits; all1100 prior types are unchanged.
The full local root/type/axiom audit has1130 heads and327 source hashes.
The interval-bijection obstruction is still open.

## Independent Gamma monotonicity

Pins unchanged. Reused the exact checked genuine tuple finite-subcover
interface and generic finite injection/cardinality equivalence. Actual
FullGammaSyntax counts distinct quotient values. No general arbitrary-value-
group monotonicity theorem was found in the pinned Mathlib/predecessor.
The earlier surveyed real-only o-minimality implementation does not apply
to non-Archimedean Gamma; no theorem or code from it is imported or ported.
Instead prove finite strict extrema using uniform positive group windows,
then two-sided signs and definable-prefix LUB propagation. All36 new full
types exactly match individual reviewed audits,including explicit dual
orders. All1130 prior types are unchanged. Full1166-head local root/type/
axiom audit and340 source hashes match; no outside citation introduced.

## Corrected3.24: independent finite interval count

Pins unchanged. No external theorem was imported. Actual finite sign codes
give finite open-cell indices. Checked Gamma image/preimage syntax and
piecewise strict monotonicity construct compatible source/target cuts.
Actual finite-controller LUBs supply every endpoint; the independent
right-endpoint count excludes nonprincipal-cut shortcuts. The actual
bijection proves equality of finite point counts. Thus Icc-to-Ioc/Iic
is impossible,including the targetVFclosed ray. PuncturedBallObstruction
assembles the approved corrected3.24 with all helper premises supplied.
All44 new full types match individual reviewed audits; all1166 prior types
are unchanged. Full1210-head local root/type/axiom audit has357 source hashes.
No Euler/Grothendieck/HK citation or referee assertion is a proof input.
