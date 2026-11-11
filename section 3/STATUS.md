# Section3: parametric balls and atomic subsets

Target: arXiv:0809.0473v2,through Proposition3.24.

The full local root build, inherited QE audit, Section2 audit and1244
Section3 type/axiom audits pass:356 generic and888 actual heads.
All368 source hashes match; all1210 previous complete types are unchanged,
and all34 new complete types exactly match individually reviewed audits.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
.scratch/local-least-radius-1244/ and VERIFICATION.json. [CI42997698267](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42997698267) passed;
all1244 full CI types and368 source hashes match the reviewed local archive. The preceding sourceb2210a7 passed
[CI42994511817](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42994511817)
and was promoted to main at receiptce43208 after exact type/source/audit matching.

## Numbered results and exact scope

Twenty-one numbered results have checked implementations in the scopes below.
Green checks certify these exported types,not broader unstated claims.

| Result | Checked conclusion and boundary |
| --- | --- |
| 3.1 | Complete-type generation and atomicity calculus for actual definable finite tuples and interpreted bases. |
| 3.2 | Parametric ball atomicity over the full real/Gamma/ball base. Actual nonalgebraicity is of the output ball name; only the input name is adjoined. |
| 3.3 | Atomicity survives every finite Gamma tuple,including mixed VF/RV tuples. ACVF00 and an original-base definable nontrivial Gamma value are explicit. The ambient is definable atomic. |
| 3.4 | CompleteTypeBallAtomicity.lemma_3_4 covers every actual open/closed ball,including arbitrary unnamed radii,singletons andVF,over the full original real/Gamma/ball base. Ambient complete type need not be definable. Genuine saturation,infinite cardinal,small original real base,ACVF00 and a genuine nontrivial value explicit. Only the actual ball name is adjoined. |
| 3.6 | Actual finite nonempty disjoint primitive decomposition of an atomic VF set,with common radius,valuative centre and primitive kind. No individual component is assumed definable. |
| 3.7 | Whole-ball coverage at the radius of an inner ball,including singleton/VF cases. Initially unnamed radius is adjoined using checked3.3. |
| 3.8 | Full partial-domain VF images preserve atomicity and the one-component condition. |
| 3.9,3.10 | Actual RV-powerset constancy in every finite RV arity on an atomic open ball,and on an arbitrary-radius open subball of a definable atomic set. |
| 3.11 | Separation.lemma_3_11 with the approved R.Nonempty correction. Both radii may be originally unnamed. |
| 3.12 | Both function obstructions,including the singleton closed-source case of the finite-to-one direction. |
| 3.13 | An actual definable VF image of an atomic open ball is constant or an atomic open ball. |
| 3.14 | Infinite one-component atomic target cannot be closed when its only ball imaginary is the source open-ball name. Original Gamma names are permitted; source radius need not be named. |
| 3.15 | FullCompleteTypeOpenImages.lemma_3_15 for the full original real/Gamma/ball base,arbitrary open-ball radii,and possibly undefinable complete-type ambients. The map may be defined on a larger definable domain. Genuine saturation,infinite cardinal,small original real base,ACVF00 and original-base definable nontrivial value are explicit. |
| 3.16 | Actual Gamma-linearity with coefficient target/source radius ratio,using actual HasRadius properties. Genuine saturation,infinite cardinal,small real base,ACVF00 and original-base definable nontrivial value are explicit. No linearity premise. |
| 3.17 | LeastLinearRadiusExistence.corollary_3_17_ordinary constructs the actual least-radius function and proves the exclusion for every ordinary open source ball; no givenleast or syntax premise. Existence needs onlyACVF00 and the full original-base partial graph. The exclusion retains genuine saturation,infinite cardinal,small real base and injectivity. Original conditional3.17 still includesVF. Actual id onVF has no leastGammaTopradius; no author correction is adopted. |
| 3.18 | Complete actual RV-linearity,with the same standing saturation/smallness/characteristic/nontrivial-value scope as3.16. The affine-error replacement avoids the printed endpoint inference. |
| 3.19 | FullOpenToOpenPartition.proposition_3_19 constructs an actual finite disjoint partition into nonempty original-base definable pieces with actual OpenToOpen. Full original base; same standing scope as3.15. No finiteness or cardinal bound on old imaginary names. |
| 3.20 | Actual coordinate slicing, scalar fibre maps, full uniform graph and restriction stability are checked. |
| 3.21 | CoordinatePartitions.proposition_3_21 constructs the full uniform finite nonempty disjoint original-base partition for all selected VF coordinate pairs of actual mixed finite tuple injections. Arbitrary finite coordinate index types include all mixed arities. Same standing saturation,smallness,ACVF00 and originally named nontrivial-value scope as3.19; no old-imaginary cardinal bound. |
| 3.22 | Complete component and actual-hole conservation for finite disjoint thin families under an original-base definable open-to-open VF bijection. Full original base; onlyACVF and a genuine nontrivial value. No canonical-model,saturation orACVF00 premise. |
| 3.23 | No definable bijection between any distinct actual atomic primitive shapes:open,closed,thin annulus. Full original base,ACVF00 and originally definable nontrivial value. No saturation or3.15 premise. |
| 3.24 | PuncturedBallObstruction.proposition_3_24 proves the author-corrected ordinary closed-parent obstruction for actual single proper open holes. The open target includesVF. Full original interpreted base; genuine saturation,infinite cardinal,small real base andACVF00 explicit. No old-imaginary bound or interval/Euler/matching premise. |

Except where a row states otherwise,the atomic unary geometry in3.6--3.13
retains its full-base ACVF00/originally definable nontrivial-value scope.
See exported full types and VERIFICATION.json for the exact hypotheses.

All21 numbered Section3 main targets now have checked implementations
in their recorded scopes;3.20 is a definition. Corrected3.24 is proved.
Ordinary-source least-radius existence in3.17 is now proved. The original
conditional theorem still coversVF; id onVF has no leastGammaTopradius.
Section2.34 remains open separately; Section2.15 is checked.

## Full-base ball atomicity and3.15

For any putative same-base cut after naming a ball,form the full-base
definable family of balls split by that relation. Specialize finite
imaginary code support only inside a compactness argument. Checked
real/Gamma open/closed ball atomicity excludes splitting balls in a complete-type
core over that real code base. Two genuine saturation steps produce a
finite real-definable cover containing no splitting-family member.
C-minimal finite ball support supplies arbitrary finite hitting points.
No original complete type is assumed complete over the auxiliary codes.

FiniteBallProfiles derives intrinsic terminal membership classes from a
laminar family with a finite hitting set. Every family ball meets a terminal
class; there are finitely many classes. Their definitions name no hitting
points. BallProfileDefinability proves their full original-base syntax.
If a family ball lies in one original complete type,the entire ball lies
in the terminal locus. TerminalBallCover and finite proper-subball
non-covering make that ball one whole terminal class. The ball-coded
terminal classes are disjoint and same-base definable. The existing
atomic_below_complete_type theorem proves atomicity over the ball name.
This contradicts the putative cut. SplittingBallHitting constructs the
hitting set; no such premise remains in the final3.4/3.15 types.

Checked3.13 and injectivity now give3.15. This proof replaces the printed
fixed-radius step for unnamed radii and old ball parameters. The finite-hitting
strategy was developed independently before the referee attachment was read. The attachment's
proposed QE bridge is not used. PROOF-WRITEUP.md records the future writeup.

## Full-base finite partitions in3.19

FiniteBaseRealPresentation supplies common finite real codes for all
definitions over a finite interpreted base. FiniteBaseTypeNeighborhoods
keeps its type core over the original interpreted base,uses full3.15 to
exclude bad ball configurations,and applies genuine saturation only over
the internal common real code set. The neighborhood remains definable over
the original base. FiniteBaseOpenImageCovers supplies the second compactness
step. The actual definable inverse gives a second finite cover; actual
preimages and checked finite Boolean refinement yield OpenToOpen pieces.

The final theorem restricts temporarily to finite imaginary support of the
domain,full map graph and original nontrivial-value definition. Every
resulting piece is already definable over this subbase,so monotonicity
returns the actual partition to the full original base. No size assumption
on the set of all old imaginary names is introduced. The argument follows
the paper's compactness proof with its parameter handling made explicit.

## Other replacement proofs

3.18 uses actual finite-fibre means and genuine saturation to make an affine
error constant or injective on a new atomic RV fibre. A pair excludes
constancy; checked3.16 forces a radius incompatible with the strict error
value bound. See PROOF-OBLIGATIONS.md; no HK citation or unproved input.

3.22 constructs exact native residue coordinates and full induced quotient
graphs for actual finite thin families. Arbitrary definable ACF conservation
is proved by finite-field Frobenius,first-order transfer and finite patches.
Tagged lines conserve actual component and hole counts. Native normalization
transports these counts back to the original model. This replaces the
printed regular-curve conservation argument; no outside citation is added.

## Unnamed closed radii in full3.4

ClosedCompleteTypeRVProfiles applies the pinned checked closed-disc
root-free theorem to finite original-base polynomial obstacles.
ClosedSelfCentredBallProfiles uses the actual closed chart with the tested
point as centre and all VF lifts of an RV radius variable. Non-strict
valuation bounds prove recentering and full quotient equality.
ClosedCompleteTypeAtomicity supplies real/Gamma atomicity for ordinary
closed balls,with singleton/VF cases supplied by earlier checked exports.
RealBallAtomicity covers every actual ball imaginary. The same intrinsic
finite-hitting argument now applies to any splitting-ball family,so
CompleteTypeBallAtomicity.lemma_3_4 has no open/closed or radius restriction.

## Coordinate partition setup

CoordinateSlices and CoordinateFibres define the actual deleted source and
output contexts. Whole-map injectivity gives scalar fibre injectivity.
CoordinateFibreSyntax proves the full uniform scalar graph from the entire
partial tuple graph. PointwiseCoordinatePartitions applies full3.19 after
adjoining precisely the finite real contexts, preserving every old imaginary.
RealParameterPromotion promotes these label names to free variables using
the pinned proved raw formula-promotion theorem. CodeSupportHull universally
quantifies valid quotient representatives, making the promoted relation
invariant for every new label tuple. No representative becomes a final name.

Full3.21 is now proved. UnaryPartitionTemplates.valid is a definable test
for an actual scalar partition, using forward open-ball images and the
swapped restricted graph for the reverse test. Real-label promotion yields
pointwise valid templates. Genuine tuple finite-subcover saturation gives
finitely many templates. PartitionTemplateCases assigns them on disjoint
parameter cases. CoordinateCellGluing uses the actual full partial tuple
graph to define whole-domain pieces, with exact scalar fibres.
CoordinatePairGluing proves actual disjointness and coverage, then discards
empty global pieces. SingleCoordinatePartition.full_base removes the finite
imaginary-support restriction. SimultaneousPartitions refines the resulting
finite covers across all VF coordinate pairs, including the empty-pair case.
Every output piece is definable over the original full base.

## Independent whole-field boundary check

Proposition324WholeFieldBoundary.counterexample constructs an actual nonempty
punctured whole field with one proper ordinary open hole. The same parent
is both open and closed by Definition2.2. Its identity has a full definable
graph, is a bijection and is OpenToOpen. The base has finitely many real
parameters and exactly an originally named nontrivial Gamma value.
The author approved exclusion of VF as closed parent; see PAPER-CORRECTIONS.md.
The correction comes from the explicit author reply, not the referee report.

FiniteOrderBounds independently derives LUB/GLB and the finite/interval
dichotomy from actual finite order controllers. FullGammaBounds applies
them to arbitrary original-base definable subsets of the actual Gamma
quotient under ACVF00. Its least-point corollary explicitly retains boundedness,
upward closure and closure from above; it does not prove the least-linearity
function exists in3.17 or the interval-bijection obstruction in3.24.

## Actual annulus quotients toward corrected3.24

AnnulusValueIntervals and PuncturedBallValueIntervals prove the exact value
images:closed Icc for the ordinary closed source,Ioc for an ordinary open
target,and Iic forVFas open target. Parent/hole centres may differ.
RadialOpenClasses proves that maximal open subballs of radial domains
avoiding their centre are exactly translated nonzeroRVfibres.
RadialClassMaps preserves and reflects those actual fibres.
RadialQuotientGraph constructs the induced actual RVbijection with its full
definable graph,adjoining exactly the two real hole-centre labels.
RadialRVImages proves that these images contain every RVclass at each
allowed value,with actual nonzero sorting.

RVFunctionValueCuts builds the full guarded Gamma cut family from the
actual partial RVgraph. Checked genuine saturation then gives finite value
image on a fixedRVvalue fibre. FullRVValueFibres supplies actual infinitude
and full-base finite/cofinite traces. CofiniteRVRows proves a unique
dominant value and a cofinite image in that entire target fibre.
RVValueMatching uses the actual definable inverse to supply a match for
every target value. Generic CofiniteClassMatching then gives a true Gamma
index bijection. The subsequent batch proves its full first-order graph; the independent
interval-bijection obstruction remains open.
No uniform bound is substituted for surjectivity. No outside citation,
referee assertion or HK result is a proof input.

## Definable Gamma matching and actual annulus reduction

RVMatchCodeRelations keeps both proper Gamma-code labels free in the
source and matched rows. FullBaseCounting expresses distinct actual RV
witnesses over the original interpreted base. RVMatchUniformBound uses
finite formula support only internally to obtain a genuine uniform bound
for the finite side of every proper code row. RVMatchRowSemantics identifies
cofiniteness with the exact actual two-sided matching relation.
DefinableGammaMatching.exists_definable_gamma_bijection now constructs the
actual index bijection with its full original-base first-order graph.
All proper representatives remain in that graph. Saturation,an infinite
cardinal,small real base and ACVF00 are explicit; no old-imaginary bound.

RadialAnnulusDomains and RadialValuePullbacks identify the actual bodies
and their complete RV images. AnnulusGammaReduction.closed_to_open gives
a definable bijection from the closed source Icc to the ordinary-open
target Ioc or the VFtarget Iic,adjoining exactly two real hole-centre labels.
This is a checked reduction. It does not prove the interval obstruction
or corrected3.24. No outside theorem or referee claim is a proof input.

## Actual Gamma piecewise strict monotonicity

FullGammaCounting counts distinct actual quotient values using the full
original-base syntax. FullGammaUniformFiniteness derives a genuine uniform
bound from small-base finite-subcover saturation, specializing only the
finite formula support internally. OrderedLocalExtrema uses positive
multiplicative windows and N+1 points to exclude an interval of strict
minima. Finite controllers then give finiteness. GammaExtremumSyntax and
GammaLocalExtrema supply all actual definability and bound inputs, for
both minima and maxima. No countability or Archimedean premise is used.

FiniteOrderGerms gives one-sided constant comparison cuts.
OrderedFunctionGerms classifies the two strict signs for actual injections.
GammaGermSyntax constructs the full-base increasing-set and prefix syntax;
GammaTupleParameters specializes only the actual finite Gamma labels.
OrderedGermMonotonicity propagates signs using the actual prefix LUB.
GammaPiecewiseMonotonicity.exists_cuts constructs finite cuts so every
cut-free open interval in the actual domain has StrictMonoOn or StrictAntiOn.
Genuine saturation,an infinite cardinal,small original real base andACVF00
are explicit. No old-imaginary bound or monotonicity premise is supplied.

This independently proved step supports corrected3.24. The finite
interval-counting obstruction and the final punctured-ball assembly remain
open. No unproved Euler/HK result or referee claim is a proof input.

## Corrected Proposition3.24

PuncturedBallObstruction.proposition_3_24 proves the approved statement.
The source parent is an ordinary closed Gamma-radius ball. Both actual
punctured balls have exactly one proper paper-open hole. The target parent
is paper-open,includingVF. The original full partial VFgraph is definable
and the actual map is a bijection. Its OpenToOpen property is impossible.
Genuine saturation,an infinite cardinal,small original real base andACVF00
are explicit. No restriction on old imaginary names or the open target.

PuncturedSingleHole excludesVFas a proper hole,proves body nonemptiness
and orders the source endpoints. The checked exact annulus/RV/Gamma
reduction gives Icc-to-Ioc or Iic. GammaIntervalObstruction independently
excludes both actual definable Gamma bijections,including singleton Icc.
FiniteOrderCells and GammaPairedCellSetup construct finite source and
target endpoint partitions. Target cuts contain all source-cut images and
control every monotone source-cell image. Their actual pullbacks are
nonempty convex endpoint-free cells. GammaCellDecomposition supplies each
actual LUB and proves its membership in the ambient interval.

OrderedFiniteCellCount sends each open cell bijectively to its right
point cell,excluding just the closed source minimum. Thus Icc has one
more point than open cell; Ioc and Iic have equal numbers. The actual
bijection gives equal point counts on paired decompositions,contradiction.
No unproved Euler/Grothendieck/HK theorem,referee claim or cell-decomposition
premise is used. Every helper Data field is constructed in the final proof.

## Ordinary least-radius existence and the VF boundary

LeastLinearRadiusExistence.ordinary constructs the actual least
GammaTopradius at every point of an ordinary source ball. The map needs
only a full original-base partial graph,VFoutputs andACVF00; no injectivity
or saturation is required for existence. ordinary_function constructs a
threshold function,and corollary_3_17_ordinary proves the exclusion without
a given least-radius function. The exclusion uses the recorded genuine
saturation,infinite cardinal,small real base and injectivity hypotheses.
No definability of the chosen threshold function is claimed here.

UniformGammaBallSyntax and UniformGammaSlopeSyntax retain every proper
radius/coefficient code. GammaLinearValueRow and GammaLinearBallRow use
actual fgraph witnesses to express both domain containment and the exact
GammaLinearity equality,including zero differences. GammaLinearRadiusSyntax
adjoins only the real centre and quantifies the coefficient codes.
OpenRadiusLimits proves actual pairwise ball union density.
GammaLinearRestrictions gives coefficient uniqueness on every ordinary ball;
GammaLinearRadiusClosure proves closure from above. Actual source inclusion
bounds the locus below. Checked finite-controller completeness supplies its
least point; an empty ordinary locus gives the singleton radius infinity.

LeastRadiusWholeFieldBoundary independently proves id onVF has a full
original-base graph and is linear at every ordinary radius,so it has no
least radius inGammaTop. This is an existence boundary,not a counterexample
to the original conditional3.17 exclusion. No author-approved correction
or new source restriction is inferred. Section2.34 remains open separately.

The subsequent Section2 volume-descent batch passes the full root and all
27 Section2 plus1244 unchanged Section3 type/axiom audits. Its concrete2.34
bridge proves both volume conditions but retains the predecessor's explicit
henselian graph or finite-extension reference input; unconditional2.34 remains
open. Evidence is in .scratch/local-volume-descent-27/,including both section
archives. [CI43002045059](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43002045059) confirms that integration batch after exact full type/source/audit matching.
