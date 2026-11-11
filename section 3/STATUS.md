# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12, through Proposition 3.24.

## Verification

The full local root build, inherited QE audit, Section 2 audit and 926
Section 3 type/axiom audits pass: 328 generic and 598 actual heads.
All 248 source hashes match; all 914 prior complete types are unchanged,
and all 12 new complete types exactly match individually reviewed audits.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
.scratch/local-primitive-distinction-926/ and VERIFICATION.json.
New CI confirmation is pending. The preceding complete3.22 source13cabca
passed [CI42960151159](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42960151159);
all914 complete types and244 hashes matched before main receipt4786753.

## Numbered results

Seventeen numbered Section 3 results are checked in the following precise scope:

- **3.2:** `AdjoinBall.lemma_3_2` permits arbitrary real, genuine Gamma and
  ball names. Atomicity is over the original base with the input ball name
  adjoined; nonalgebraicity concerns the output ball imaginary.
- **3.3:** `FullGammaAtomicity.lemma_3_3` preserves atomicity after every finite
  Gamma tuple, for every finite real tuple arity, including mixed VF/RV.
  ACVF(0,0), an original-base definable `δ` and `1 < δ` are explicit.
- **3.4:** `FullGammaRadius.lemma_3_4` proves ball atomicity at original-base
  definable Gamma radii, and for singletons and VF. The ambient complete type
  need not be definable. Only the ball name is adjoined. An extension to
  unnamed open-ball radii over real/Gamma bases is now checked as described
  below; the extension with old ball parameters remains open.
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

- **3.14:** `ClosedImageObstruction.lemma_3_14` proves that an infinite atomic
  target with one primitive component is not a closed ball when its only ball
  imaginary is the source open-ball name, and that source is atomic over its
  name. The original base may contain genuine Gamma names, but no other ball
  names. The source radius need not be originally named. ACVF(0,0) and the
  standing named nontrivial value remain explicit; no saturation is assumed.

- **3.16:** `GammaLinearity.lemma_3_16` proves actual Gamma-linearity of an
  injective partial-domain definable VF map on an atomic open ball, with
  coefficient equal to target/source radius ratio (paper: target radius
  minus source radius). Source and image radii are actual `HasRadius`
  properties; no centre or radius lift is named in the original base.
  Genuine `Saturated M kappa`, `aleph0 <= kappa`, `mk B.real < kappa`,
  ACVF00 and the original-base named nontrivial delta are explicit.
  The RV map, Gamma graph, finite image, finite controllers, order
  isomorphism and constant-shift argument are all proved. A saturation-free
  all-model transfer is not claimed.

- **3.17:** `LinearRadiusThreshold.corollary_3_17` excludes a uniform strict
  lower bound above the actual source radius for every given least-linear-radius
  function, as in the paper. `exists_at_radius` constructs an actual Gamma-linear
  subball at every prescribed ordinary radius above that source radius. The
  source includes VF with bottom radius; infinity in the threshold predicate
  means a singleton. The map may be any injective partial-domain definable VF
  map, so no image-ball premise is needed. The original full real/Gamma/ball
  base, genuine saturation, infinite saturation cardinal, small real base and
  ACVF00 are explicit. Only finitely many centre/radius codes are temporarily
  named inside the proof; no original named delta or bound on the imaginary
  base cardinality is required. The definition of least radius does not
  assert existence of a least-radius function.

- **3.18:** `RVLinearity.lemma_3_18` proves actual RV-linearity on an atomic
  open source, for its full original-base partial-domain graph and any
  injective VF map. The coefficient is an actual nonzero RV element and
  its equation holds for every pair, including equal points. Image openness
  is derived. Genuine saturation, infinite cardinal, small real base,
  ACVF00 and an original-base named nontrivial Gamma value remain explicit.
  Temporary real codes and the error map occur only inside the proof.
  Injectivity of that error map is proved from finite-fibre means. Checked
  3.16 then gives a radius contradiction, avoiding the printed endpoint
  estimate without a statement correction or an unproved external input.

Section 2's Corollary 2.15 is checked separately, with genuine saturation and
parameter smallness explicit. Corollary 2.34 remains open.

- **3.22:** ThinFamilyConservation.lemma_3_22 proves both actual finite counts
  over the full original interpreted base, with ACVF and explicit nontrivial
  Gamma value. No canonical-model or saturation premise remains.

- **3.23:** AtomicPrimitiveDistinction.proposition_3_23 excludes a definable
  bijection for every ordered pair of distinct actual atomic open, closed
  and thin-annulus shapes. Full original base, ACVF00 and originally named
  nontrivial Gamma value are explicit. No saturation or unrestricted3.15.

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

Four proof results remain: 3.15, 3.19, 3.21 and 3.24; 3.20 is a definition.
They comprise one lemma and three propositions. Section 2's 2.34
is open separately. The extension of 3.4 and 3.15 with old ball parameters remains open.
Arbitrary open-ball radii over real/Gamma bases are now checked, including
a possibly undefinable complete-type ambient. A wrapper for arbitrary-radius subballs
of a **definable atomic** ambient set is checked separately, but it does not
replace3.15 for a possibly undefinable complete-type set.

## The 3.14 coefficient and escape argument

`BallCentreElimination` replaces the source ball name by every one of its real
centres, while keeping the subgroup definable over the old base. Only actual
Gamma names remain there. `GammaSpecialization` specializes their finite code
support using RV representatives and original VF0/1 constants and proves the
VF parameter field unchanged. `GammaPairFormula` then applies the pinned
quantifier-elimination theorem to a two-VF-variable formula with coefficients
in exactly that original parameter field.

`MultivariatePolynomialSupport` extends the pinned MIT unary support argument
to a finite VF tuple, reusing `Section4.MultivariateSyntax`. Finite polynomial
support controls truth of every well-sorted quantifier-free formula. Original
source attribution is retained. `AtomicPolynomialRoots` proves that nonzero
polynomials cannot specialize identically on the infinite atomic source.
`PolynomialSeparation` turns any purported zero into a nonempty definable
relation with finite source rows, contradicting corrected 3.11.

`PolynomialEscape` supplies an outside point with the same RV values for all
specialized polynomials on the root-free closed target. Truth preservation
contradicts its defining formula. The source radius is temporarily adjoined
using3.3; the final statement names no centre or field-radius lift. All these
steps are proved, not assumed as a polynomial-presentation interface.

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

## RV difference maps toward 3.16

The next 28 declarations passed individual and full integration type/axiom
checks. They prove that an
injective full-base definable VF map on a definable atomic open ball
preserves and reflects equality of RV difference classes, even for pairs
with different base points. Its common RV relation also respects nonzero
natural-number multiplication. No radius or centre is named in the
original parameter base, and no saturation premise is used here.

`OpenSubballImages` handles arbitrary-radius subballs of a definable atomic
ambient set. `RVFibreSubballs`, `RVPairPreservation`, `RVDifferencePairs`
and `RVPairConstancy` supply the actual subball geometry and full graph.
`RVMapRelation`, `RVInverse` and `RVMapBijection` establish the common
single-valued bijection. `ValuationProgressions`, `RVIntegerSequences`
and `RVIntegerEquivariance` give the integer argument. The full 3.16
Gamma-linearity conclusion is now assembled from these components and the
subsequent order argument. Unrestricted 3.15 remains open independently.

## Gamma slope fibres and valuation order toward 3.16

The next 21 components are fully locally integrated. `RVInputFibre` realizes
all relevant RV classes in the source ball. `RVSlopeGraph` retains the full
original-base coefficient graph; `RVSlopeFibres` proves coefficients exist
and are unique. `RVIntegerOrbits` and `RVSlopeOrbits` make every nonempty
coefficient fibre infinite. `RVSlopeFiniteCofinite` applies the pinned checked
RV value-fibre dichotomy; `RVSlopeConstancy` proves a coefficient is constant
on each actual Gamma value fibre, without saturation.

`RVSlopeGamma` descends to a full-code Gamma relation. Its finite-image
theorem explicitly assumes genuine saturation, an infinite saturation
cardinal and a small real part of the base, exactly as the checked finite
projection theorem requires. Finite imaginary support is specialized only
inside the proof. `OpenBallSeparationGeometry` and `InjectiveBallOrder`
prove preservation of strict valuation comparisons using actual open
subball images; this step needs no saturation.

The previously remaining constant-slope and radius-identification steps are
now proved, as described below. The unrestricted 3.15 issue is unchanged.

## Assembled Gamma-linearity 3.16

`GammaDifferenceRealization` and `GammaSlopeDomain` identify the source
Gamma tail exactly. `GammaSlopeOutput` proves the actual output-value
formula for every source pair. `GammaTailMap` constructs a strictly
increasing map, and `GammaTailIso` proves surjectivity by lifting actual
image points, obtaining an order isomorphism of the source/image tails.

`FullGammaControllers` and `GammaSlopeValueGraph` prove finite order
controllers for every shift fibre over the full interpreted base.
`FiniteImageContinuity` proves local constancy for continuous finite-range
maps; `FiniteControllerLocal` and `GammaShiftConstancy` then prove global
constant shift and identify it with the ratio of endpoint radii. This
argument does not assume a complete or Archimedean value group.

`GammaTailShift` supplies every prerequisite of that abstract order step.
`GammaLinearity.ordinary` gives the actual field-value equation, including
zero differences. `GammaLinearity.lemma_3_16` removes selected centres and
uses actual radius invariants. All 28 new full exported types match the
reviewed individual audits. Saturation and smallness enter through the
already checked finite Gamma-to-RV projection; no such premise is hidden
inside the definition of Gamma-linearity or assumed as the desired result.

## Nonalgebraic subballs and Corollary 3.17

`SaturatedInterpretedFamilies` realizes a real point outside every finite
base-definable subfamily of an infinite disjoint family. Its index is then
nonalgebraic. `SaturatedBallFamilies` transfers genuine saturation through
the proved normalization reduct and applies this to actual ball membership.
It does not introduce saturation of an imaginary quotient sort.

`BetaSubballFamilies` gives full-code definability, coverage, disjointness,
actual fixed-radius presentations and infinitude of the smaller-ball family.
`NamedBallSetup` defines radii and ball fibres from temporarily named real
codes. `AtomicBallFamilyChoice` supplies the full interpreted identity graph
and applies checked 3.2. `LocalGammaLinearity` restricts the map graph to the
chosen atomic member, proves its image is open and applies checked 3.16.

`LinearSubballSpecialization` removes the intermediate named-centre/radius
hypotheses by specializing only the finite support of the original map.
The small real base remains small after the finite enlargement, regardless
of the cardinality of the original imaginary base. `LinearRadiusThreshold`
handles actual radius invariants, including VF and infinity, and derives
3.17 for every given least-radius function. All 21 full exported types match
the reviewed individual audits; all 707 preceding full types are unchanged.

## RV-linearity components and the replacement proof of 3.18

`RVValueShellGeometry` identifies actual nonzero RV fibres with ordinary open
balls and proves that each value shell has infinite RV image, using the
checked ACVF00 integer orbit. `RVValueBallFamilies` supplies a full-code
infinite disjoint family and an actual atomic fibre through genuine real
saturation and checked 3.2. Its intermediate base is small and has no
imaginary parameters; saturation of an imaginary sort is never assumed.

`RVSlopeControllers` proves finite order controllers for each coefficient
row, naming that RV coefficient only inside the row proof.
`FiniteControllerTails` bounds the finite union of endpoints; `RVSlopeTail`
then proves that the actual nonzero RV coefficient is constant above some
Gamma value larger than the source radius. This is eventual constancy,
with all genuine saturation/small-base hypotheses explicit.

`RVUnaryConstancy` derives ordinary unary RV-map constancy from 3.9.
`RVErrorSyntax` represents the actual affine error by normalized first-order
syntax and proves its full partial-domain graph is definable when its three
real constants are named. `RVErrorConstancy` proves equality of actual RV
errors on an atomic open source. `RVErrorComparison` supplies the strict
error-value estimate and affine RV-difference recovery, including zero error.

The full 3.18 result is now proved by a different ending.
`VFExchangeAnyBase` extends the pinned VF exchange proof to every real base.
`FiniteFibresFromExchange` and `AtomicFunctionFibres` prove that a real-base
map, restricted to an atomic open ball, is constant or has finite fibres.
The finite-code specialization and genuine saturation needed for finiteness
are proved with their cardinal bounds explicit.

`FullFibreEnumerations`, `FullFibreMeans` and `AtomicFibreMeanGraph` define
the actual fibre means over the unchanged full interpreted base. The bound
on fibre size is supplied by completeness of the image. Checked RV
nonconstancy of a finite mean-centred set and 3.9 give injectivity in
`FiniteFibreInjectivity` and `AtomicFunctionInjectivity`.

`RealGraphOperations`, `VFErrorSyntax`, `TranslationSyntax` and
`TranslatedErrorGeometry` construct the real-definable translated error.
`RVLinearitySlopeValues`, `RVSlopePairFormula` and `RVLeadingDifference`
give its strict output bound and an exact pair-value equation if two
original RV coefficients differ. `RealAtomicValueBoundRigidity` supplies
error-map injectivity and applies `AtomicValueBoundRigidity`: checked 3.16
forces its open image to contain zero, contradicting atomicity.

`RVSlopeRigidity.ordered_coefficients_eq` applies that contradiction on a
newly chosen atomic RV fibre after finite temporary naming. The original
whole source need not remain atomic over the enlarged real base.
`RVLinearity.lemma_3_18` supplies the intermediate Gamma-linear premise
from checked 3.16 and proves the final equation on all source pairs. The
printed endpoint issue is documented in
[PROOF-OBLIGATIONS.md](PROOF-OBLIGATIONS.md); that inference is not used.
The mathematical replacement is tracked for the author's requested final
writeup in `../PROOF-WRITEUP.md`.

## Unnamed radii and possibly undefinable complete types

`CompleteTypeRVProfiles` gives a QF presentation for every real/Gamma-base
RV relation with VF coefficients in exactly the original real parameter
field. A finite original-base definable polynomial obstacle set controls
all RV tuples simultaneously. An infinite complete-type ambient excludes
this finite set, so the relation is constant on every open ball it contains.
The ambient complete type is never assumed definable.

`SelfCentredBallProfiles` replaces the centre in a named ball's code by the
point being tested, retaining its radius as an RV variable. All radius lifts
are quantified, and native normalization and quotient equality are proved.
The profile has just one VF variable; the preceding obstacle argument
therefore applies without naming the ball radius in the original base.

`OpenCompleteTypeAtomicity.lemma_3_4_open_gamma_base` concludes actual
atomicity over the original base plus the one ball name. It has no saturation
or original named-radius premise. `CompleteTypeOpenImages.lemma_3_15_gamma_base`
then applies checked 3.13 and rules out a constant image by injectivity.
It permits a graph on any definable larger domain containing the complete
type. ACVF00 and the standing original-base named nontrivial Gamma value
are explicit. Its whole-VF case is excluded by the parameter-free zero.

The original base in these new conclusions may contain arbitrary real and
Gamma parameters, but no old ball parameters. That restriction is explicit
in every relevant exported type. Thus unrestricted 3.15 remains on the six
remaining-result list. No unproved full-base extension is assumed or counted.

## Complete component and hole conservation, Lemma 3.22

Lemma 3.22 is complete in ThinFamilyConservation.lemma_3_22 over the full
original real/Gamma/ball base. Finite actual thin families with pairwise
disjoint bodies, the original-base full partial VF graph, actual BijOn,
actual OpenToOpen and a genuine nontrivial Gamma value are the inputs.
Both original component counts and sums of actual hole cardinalities
are equal. No canonical-model restriction, saturation, ACVF00 or originally
named charts, centres, radii or tags occur in the final theorem.

The proof constructs exact native residue coordinates for each actual
closed parent and its finite holes. FiniteTaggedHoles and
FiniteFamilyCoordinates give the exact cofinite tagged line union and
correct actual counts. FiniteFamilyMaximal proves intrinsic maximal
fibres; FiniteFamilySyntax eliminates representative choices from the
full LRV graph. Open-to-open kernel preservation and the general quotient
theorem construct the actual induced bijection. RVQuotientGraph proves
its complete RV graph as an existential image of the original VF graph.
ThinComponentConservation applies checked native residue conservation.

NormalizedBallParameters transports entire same-radius families using a
common RV code, retaining distinct Gamma quotient types.
NormalizedThinGeometry preserves actual parents, holes, bodies and
openness in both directions. NormalizedNontrivialValue supplies a genuinely
nontrivial normalized value. NormalizedThinFamilies preserves component
and total-hole counts through an explicit finite equivalence. Finite
imaginary support specializes only inside the intrinsic-count proof;
the final equality transports back to the original actual families.

Pure-field conservation is proved by finite-field Frobenius, finite
formula support, ACF first-order transfer and definable finite patches.
The pinned predecessor supplies proved residue purity and actual ball
normalization; no new outside citation, unproved conservation or HK
input is used. The patching argument replaces the printed regular-curve
conservation step and is recorded for the final whole-paper writeup.

## Complete primitive-shape distinction, Proposition3.23

Proposition 3.23 is complete in
AtomicPrimitiveDistinction.proposition_3_23 for every ordered pair of
distinct actual primitive shapes: open ball, closed ball and thin annulus.
The original full real/Gamma/ball base, atomic source and target, complete
partial VF graph, ACVF00 and an original-base definable nontrivial Gamma
value remain explicit. No saturation or unrestricted3.15 premise is used.

AtomicOpenToOpen proves that actual definable atomic source/target VF
sets have the open-to-open property. It applies already checked
arbitrary-radius OpenSubballImages in both directions with the actual
definable inverse graph. This is the definable atomic ambient case;
it does not assert3.15 for arbitrary undefinable complete-type sets.

ThinBallHoleConservation gives actual one-component hole equality from
complete3.22. ThinBallGeometry realizes an ordinary closed ball with
zero holes, proves an actual thin annulus has the required thin
presentation, and proves thin-body infinitude from an actual open subball.
The closed/thin case is therefore the contradiction0=1. Singleton
closed balls are excluded by thin-body infinitude; VF is excluded by
atomicity. Open cases use the checked finite-to-one separation theorem
on an actual inverse with finite actual fibres. The final theorem checks
all six ordered pairs, with the three diagonal cases excluded by the
stated inequality of primitive kinds.
