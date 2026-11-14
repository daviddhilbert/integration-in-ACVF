# Writeup of substantially different proofs

Requested by the author on November 10, 2026 (America/Los_Angeles).
**After formalization of the whole paper is complete**, prepare a mathematical
writeup of proofs that differ substantially from those in arXiv:0809.0473v2.
This is a future deliverable for the whole paper, not just Sections 1–3.

Keep this ledger current as results are completed. The final writeup should
explain the mathematical argument in ordinary prose and include:

- The numbered statement and its exact hypotheses or author-approved correction.
- A brief account of the paper's proof and the substantive difference.
- The complete replacement argument, including important intermediate lemmas.
- Why the replacement was chosen and any change in scope or assumptions.
- Links to the final checked Lean declarations and verification checkpoint.

Distinguish mathematical changes from routine encoding, syntax and compiler
work. Recheck each candidate against the final proof before including it.
Preserve the author's existing citation policy; consultation for ideas does
not authorize a new cited theorem or unproved input.

## Current ledger

| Result | Candidate difference | Current state |
| --- | --- | --- |
| Corrected 3.11 | The checked proof uses atomic uniform finite-fibre bounds, canonical inverse supports, intrinsic closed hulls and finite/cofinite quotient traces. Review the exact difference from the printed compactness/cut argument for the final writeup. Keep the approved nonemptiness correction separate from proof differences. | Verified on main; inspect `section 3/IntegrationSection3ACVF/Separation.lean` and its supporting modules. |
| 3.4 and 3.15, real/Gamma-base scope | Replace the new ball's centre by the tested point and leave its radius as an RV variable. A finite original-base polynomial obstacle set controls all RV parameters; the possibly undefinable complete type excludes that set. This supplies unnamed-radius ball atomicity, then open images via 3.13. | Checked in the full 805-head local audit and CI 42949057513; every complete type and source hash matches. This remains the saturation-free real/Gamma proof. Full-base open-ball3.4/3.15 is now supplied by the separate finite-hitting replacement below. Inspect `CompleteTypeRVProfiles`, `SelfCentredBallProfiles`, `OpenCompleteTypeAtomicity` and `CompleteTypeOpenImages`. |
| Full-base3.4 and3.15 | For a putative ball-indexed cut,construct finite hitting points for its full-base definable splitting-ball family using internal real-code compactness and C-minimal finite support. Intrinsic maximal membership profiles have finitely many disjoint terminal classes; finite proper-subball non-covering makes the inner ball one whole class. Checked disjoint-family atomicity contradicts the cut,then3.13 gives the open image. This replaces the printed fixed-radius step without extending an undefinable type over auxiliary parameters. | Checked in the fresh full969-head local audit; all943 published types unchanged and all26 new types match individual reviewed audits. CI42967337352 passed; all complete types and source hashes match. Full original base; genuine saturation,infinite cardinal,small real base,ACVF00 and a nontrivial value explicit(originally definable for3.15). The unnamed closed-ball case is now included in CompleteTypeBallAtomicity.lemma_3_4,checked in the983-head local audit and CI42968768615,with all full types and hashes matched. Add ClosedCompleteTypeRVProfiles,ClosedSelfCentredBallProfiles,RealBallAtomicity andSplittingBallFamilyHitting to the final comparison. Inspect FiniteBallProfiles,TerminalBallCover,BallProfileDefinability,FiniteHittingAtomicity,RealSplittingBallAvoidance,SplittingBallHitting,FullOpenCompleteTypeAtomicity andFullCompleteTypeOpenImages. |
| 3.16 | The constant Gamma shift is proved using continuity of an order isomorphism, finite image, local constancy and finite order controllers, followed by identification of the radius ratio. This supplies an explicit argument valid in a non-Archimedean value group. | Verified on main; inspect `GammaShiftConstancy`, `FiniteControllerLocal`, `GammaTailShift` and `GammaLinearity` in `section 3/IntegrationSection3ACVF/`. Genuine saturation and small-base hypotheses remain explicit. |
| 3.17 | The small atomic subball is constructed through real-point saturation, a nonalgebraic interpreted-family index and checked 3.2. Assess whether this is substantive enough for the final writeup or supporting detail for the paper's argument. | Verified on main; inspect `SaturatedInterpretedFamilies`, `AtomicBallFamilyChoice`, `LinearSubballSpecialization` and `LinearRadiusThreshold`. |
| 3.18 | Definable finite-fibre means make an affine-error map constant or injective on a newly chosen atomic RV fibre. A pair with a different coefficient rules out constancy. Checked Gamma-linearity then forces an image radius incompatible with the strict value bound: the atomic image would contain zero. This replaces the printed endpoint argument. | The complete `RVLinearity.lemma_3_18` is checked in the fresh full 794-head local integration audit and CI 42947193955; all complete types and source hashes match. Keep genuine saturation, infinite cardinal, small real base, ACVF00 and the original-base named nontrivial Gamma value explicit. |
| 3.22 | Finite-field Frobenius and ACF transfer prove arbitrary definable self-map surjectivity. Definable finite patches conserve finite complements; tagged-line comparison gives components and holes directly, replacing the printed regular-injection conservation step. Actual residue coordinates and the full induced graph connect this to the original ball families. | Complete ThinFamilyConservation.lemma_3_22 is checked in the full 914-head local audit and CI 42960151159; every complete type and source hash matches. Full original interpreted base and actual finite counts; no canonical-model restriction, saturation or ACVF00 premise. Inspect ACFDefinableInjection, CofiniteDefinableInjection, TaggedCofiniteConservation, ThinComponentConservation and ThinFamilyConservation with their native coordinate and normalization bridges. |

Add entries from later sections as their proofs are completed. The final
selection and writeup must describe the final implementation, omitting
abandoned approaches unless they explain a mathematical choice.

## 3.21 comparison note

CoordinatePartitions.proposition_3_21 follows the paper's compactness and
finite refinement strategy. The formal development makes the validity
predicate,real-label promotion with invariant code hulls,and full-graph
gluing explicit. Simultaneous Boolean refinement replaces iterative pair
refinement,but does not constitute a substantially different mathematical
proof. No standalone replacement writeup is currently required for3.21.
Local1042-head audit and CI42974291389 passed; exact full type/source/audit hashes matched. The3.4 and3.18 replacement entries
remain relevant for the eventual whole-paper writeup.

## Completed corrected3.24 route for the future proof comparison

PuncturedBallObstruction.proposition_3_24 now closes the author-approved
ordinary closed-parent statement,includingVFas open target. Actual maximal
open classes give the full definable RVquotient. Dominant cofinite matching,
with the actual inverse supplying every target value,constructs the full
definable Gamma bijection. Exact values are Icc for the source,Ioc for an
ordinary open target,and Iic forVFtarget.

The Gamma obstruction is independently proved from finite paired point/
open-cell decompositions. Piecewise strict monotonicity holds in arbitrary
possibly non-Archimedean Gamma via uniform positive windows and actual
prefix LUBs. Target cuts control source-cell images and contain the images
of source cuts. Actual pullback cells are convex and endpoint-free. Their
actual LUBs lie in the ambient interval. Sending cells to right point
endpoints counts Icc as one more point than open cell and Ioc/Iic as equal
numbers; bijectivity preserves the point count,contradiction.

No unproved Euler/Grothendieck theorem or HK citation is used. This is a
completed proof route to compare with the printed proof in the requested
whole-paper writeup. Ordinary syntax details alone are not claimed to be
substantially different mathematics. Keep the approved boundary repair
separate from proof comparison. The3.17 existence boundary remains separate.

## 3.17 ordinary existence followup

Actual least-radius existence on ordinary source balls is now proved.
The full raw partial graph defines the linear-radius locus. Coefficients
on concentric ordinary balls agree by cancellation; pairwise ball union
density proves closure from above. Actual inclusion bounds the locus below,
and finite-controller completeness supplies the least radius. An empty
ordinary locus yields the singleton infinity. This fills the ordinary
existence step behind the exclusion; it does not alone change its printed
proof. VFis a separate existence boundary:its identity has no leastGammaTop
radius. No author correction is adopted and no threshold-definability
conclusion is claimed. Keep this separate in the eventual whole-paper writeup.


## Completed 2.34 route for the future proof comparison

The all-degree concrete volume descent now has all graph and finite-extension
obligations supplied by checked proofs. The generic RV comparison is combined
with actual fibre avoidance and VF-Jacobian uniqueness. The Gamma equation is
proved on every label fibre by the separate constant-value polydisc descent
argument, retaining labels omitted by the generic RV comparison. The false
unrestricted Gamma clause of predecessor9.15 is not used.

The field input is independently proved: lift Hensel roots in an algebraically
closed Galois envelope and descend them through its fixed field. Lift residue-
independent families to obtain finite residue degree,then lift a primitive
residue generator. Its subextension has exactly that degree and the full
residue field. Equal values plus residue surjectivity give immediate
approximation; trace as the sum of all embeddings makes the remaining finite
extension trivial. This applies to non-Galois finite extensions. Every field-
image,scalar and valuation-ring transport is constructed.

Inspect EmbeddedFiniteResidueDegree,ConstructedGaussGraph,
VolumeDescentTheorem andVolumeDescentAllDegrees in section2/IntegrationSection2.
The complete local audits of 68 Section 2 and 1,244 Section 3 heads pass. [CI 43010073720](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43010073720) passed.
All complete types and source/audit hashes match the reviewed local batch
and publication checkout. Keep the final whole-paper comparison
focused on the mathematical changes,not routine Lean transport. No new
outside citation,HK theorem or referee claim is a proof input.


## Verified replacement for Remark5.3

The paper passes from VF algebraicity to RV algebraicity to recognize the
induced map as an RV[1,·] isomorphism. The checked proof establishes the two
actual category conditions directly. For a fixed input VF value x, vary the
old RV labels. The complete original-Gamma graph has finite real support;
after adjoining x, its RV-to-VF relation has singleton output fibres. The
checked finite-image theorem therefore makes its VF output finite. Every
RV key with a given first value has a representative with that same x,
because the source is an RV-pullback. Contractibility identifies the key
map there, so the target volume image is finite. Apply the argument to the
actual inverse as well.

For weight, the zero RV cell is a singleton whereas a nonzero cell has two
distinct points: if x≠0 and a nonzero ε has valuation below1, then x+xε
has the same RV class as x and differs from it. A mutually contractible
bijection between RV-pullbacks consequently preserves zero versus nonzero
VF coordinates in both directions. This proves unary weight preservation.
The actual descended definable maps satisfy the inverse laws and retain
full invariant original-Gamma graphs, yielding the pinned category Iso.

Verified locally in the227-head full type/allowed-axiom audit and full
root/project checks; exact source and scope in section5/VERIFICATION.json.
Inspect `UnaryVFFibreFinite.unary_vf_fibre_image_finite`,
`UnaryVolumeImages.rvContractionMap_finite_volume_images`,
`UnaryCellZeros.unary_bijection_zero_iff`, `UnaryRVIsomorphism.unaryRVIso`
and `UnaryRVCategory.lemma_5_3`. The standalone result needs ACVF, genuine
saturation with aleph0≤κ and small original P.real, together with the
actual prepared bijection data from5.2. No internal code-set smallness or
additional algebraicity theorem is assumed. Recheck this comparison against
the final implementation for the whole-paper writeup.

## Section 4: relation preparation in 4.2–4.4

The checked 4.2 construction prepares the full radius/slope relation rather
than choosing a definable least-radius function. On an ordinary inverse ball,
constancy of this relation transfers the checked existence of linear subballs
at every strictly smaller ball scale to its centre. Closure of the linear-radius
locus supplies linearity on the whole ball. A simultaneously prepared finite
open-to-open partition supplies the second property. Zero inverse fibres are
singletons and are treated separately. This is a completed replacement route
for comparison with the printed proof, retaining all standing hypotheses.

Corrected 4.3 prepares the complete source/image radius relation, with both
ordinary radii free. Equal-radius open image balls that meet are equal;
injectivity then identifies their source balls. Uniformity on an inverse RV
piece makes the set of source radii have at most one element. A whole-field
source candidate is handled directly by image containment and the same
intersection argument. Thus one preparation works for all ordinary target
radii. Keep the author-approved empty-set correction separate from comparison
of proofs.

For 4.4 the inverse-difference relation is prepared directly. A nonzero
translated RV fibre lies in an open subball excluding the positioning value.
Its inverse image under the open-to-open bijection is an open ball missing
the original point, so RV differences are constant there. The zero case is
handled by injectivity. Preparing the full relation yields a singleton range
on each inverse piece. These are independently proved Lean arguments;
no HK result or annotated-referee claim is a proof input.

## Section 4: uniform families and completed decomposition

The checked vertical construction retains the complementary VF coordinates
through barycentric root reduction. Descending its inverse head displacement
produces one positioning map, uniformly in the first VF coordinate and all
RV labels, and identifies every actual vertical fibre as a translated RV
class. This replaces pointwise preparations and informal compactness gluing
by an explicit uniform construction.

For scalar positioning families, the locally constant image is finite:
otherwise a nonalgebraic output, VF exchange, and finite fibres from exchange
would force an entire open constant ball to be finite. Off the locally
constant locus, a fibre without an open subball is finite by finite polynomial
obstacles. Uniform finite-family bounds and intrinsic barycentric RV codes
therefore give constant or injective refinements. Every context remains a
free variable, and all intermediate means and imaginary representatives
remain quantified in the original-base graph.

Uniform linear preparation carries these contexts through the complete
radius/slope relation and the checked coordinate open-to-open partition.
An ordinary ball's open image under a Gamma-linear map has radius multiplied
by the slope. Thus an entire nonzero difference RV class maps onto its entire
output difference class. The singleton inverse-difference conclusion gives
the forward containment in the balanced horizontal identity; this class-image
equality gives the reverse containment.

The full 4.8 theorem constructs the finite-arity original-base RV map.
Uniform vertical charts retain the first VF coordinate. The actual scalar
preparations split by positioning-image radius. Tagged RV maps glue the
branches, and complete fibre identities identify their actual two-cells.
There is no cell-existence or compactness-gluing hypothesis.

All cell ingredients are proved definable over the output RV tuple.
The uniform positioning graph quantifies its intermediate mixed point;
RV-label specialization retains the original Gamma base. Both paradigms
are recovered as definable singleton ranges of actual RV differences,
including every possible balanced first paradigm. Verification evidence
and exact source identities are recorded by the Section 4 verifier.

## Section 4: balanced geometry and singleton boundary

The nonzero translated RV class is an ordinary open ball with radius equal
to the paradigm value. Valuation density proves the positioning point is a
centre of its minimal closed hull. Reversing differences gives the first
balanced hull as well. Both paradigm radii lie strictly inside the projection
balls. The slope formula and open-to-open property identify the images of
all balls at those radii. Injectivity and surjectivity give the actual ball
bijection, and constancy of translated fibres gives the two rectangle unions
expressing internal symmetry. These are checked geometric consequences,
separate from definability and cell-decomposition existence.

The unqualified open-polydisc observation after 4.7 has a singleton first-cell
boundary. OpenPolydiscBoundary proves the actual definable counterexample;
CellRectangles proves the product-of-a-1-cell-and-an-open-ball conclusion and
the open-polydisc version with open first projection. The author approved
“a product of a 1-cell and an open ball” as the replacement for the printed
open-polydisc claim. This approved statement correction is recorded
separately from comparison of mathematical proof routes.

## Section5: Lemma5.6 by scalar refinement and finite active-coordinate induction

Verified in the683-head Section5 batch: lemma_5_6 and lemma_5_6_iso, with
actual finite Gamma partitions and existing UnaryChains over one common
internal real presentation. Full types, allowed axioms and root/project
integration pass. Positive VF arity is explicit; the standing scope is
ACVF00, genuine saturation, aleph0≤κ, small original real base and a named
nontrivial Gamma value. No working-code smallness or VFFieldBase is assumed.

The paper prepares each one-VF-dimensional image by standard contractions,
uses the RV-weight dimension bound and the inverse-coordinate observation,
and then invokes compactness in the coordinate induction. The checked proof
instead refines all output scalar coordinates simultaneously into constant
or injective branches on source-head fibres, uniformly in every frozen VF
coordinate and old RV label. If all outputs are constant, the inverse head
scalar at their fixed full VF tuple has finite image as its RV labels vary.
A finite-family code separates the remaining source points. Thus every
refined fibre has an injective output coordinate without using5.5's lift
claim or a dimension argument.

A finite first-tag partition chooses the coordinate. If that coordinate is
already fixed by the remaining map, its injectivity makes the source fibre
a singleton, so an active coordinate can be chosen. Attaching the RV code
and replacing the selected input coordinate by the chosen output scalar are
actual relatively unary bijections onto their actual images. Three explicit
additive/subtractive unary updates implement any needed coordinate swap.
The remaining bijection fixes one additional coordinate. Strong induction
on the finite active-coordinate set, with definable pullbacks and finite
gluing, constructs the complete partition and factor chains. A checked
realization and parameter-extension argument gives one common real
presentation while retaining every factor's full original-Gamma graph.

This is a replacement proof of5.6 only. Its scalar replacements and swaps
are not asserted to have Jacobian1; the distinct measure-preserving
assertion used later in Section7 requires its own proof. No HK theorem or
annotated-referee claim is a proof input.

## Section 6 localization (verified)

The checked `IntegrationInACVF.Section6.GradedLocalization` development
constructs dehomogenization in an arbitrary nonnegatively graded commutative
ring: a degree-k element a maps to a/j^k in the localization at a degree-one
element j. It proves that its kernel is exactly (j-1), including when j has
torsion, by evaluating the localization in R/(j-1). In that quotient j=1,
so this evaluation composed with dehomogenization is the quotient map.
This gives injectivity directly, without first presenting the degree-zero
localization piece as a graded colimit.

The generic algebraic argument is source-compiled and its ten exported theorem
types have passed the Section 6 allowed-axiom audit. The native application to 6.22 is now verified: nonzero-label compression,
the actual principal ideal (j−1), the completion quotient equivalence and
`FiniteRV.theorem_6_22` supply all geometric bridges. The checked completion
localization implements the evaluation argument. The direct native graded
colimit universal property is also proved in `IntegrationGradedColimit`.
No outside citation or additional Section 6 premise is used.

## Section 6 finite witness uniformity

The checked RV-indexed common-blowup argument does not assert definability
of Isp. Actual finite objects, isomorphism charts, admissibility conditions
and exact-length chains have full original-Gamma formula schemata with
definable validity. Genuine compactness supplies a finite cover by valid
witnesses. Restricting the finite-volume RV index base to the validity
loci and gluing actual common blowups produces a global witness. The
index set may be infinite; finiteness is required only of its volume fibres.

For VF parameters, a single finite RV code controls every domain, volume
and chart formula in the finite witness cover. Preparing this code makes
all primitive rows constant on prepared polydiscs. The complete formulas
descend to RV keys, including their properness conditions; exact row
agreement then transports validity of every internal object and chart.
The prepared base is an actual RV[p] object, so the first argument glues
the descended witnesses in RV[p+k]. Only the original real/Gamma names
enter compactness; internal representative sets need no smallness bound.

These arguments are verified through the399-module,1,171-declaration
audit and root build. Their relation to the printed proof of6.14 must
be assessed again after the comparison with arbitrary standard contractions
is complete. They are established uniformity ingredients, not a claim
that6.14 or the whole Section 6 is finished.


### Section 6: eliminating internally named coefficient fields

Unary lift comparison and VF-parameter witness preparation can be used
over an arbitrary small base under uncountable saturation. Internally name
the VF field generated by its real parameters. Every added name is already
definable over the original base; the generated field remains small by the
checked cardinal bound for field generation. Eliminate these names from
full formulas and from every chart, centre and admissibility certificate of
the actual blowup witnesses. For VF preparation, one finite RV code controls
the original primitive witness rows, even though its construction uses the
internal field. Eliminate the names from the special chain before descending
the rows. Thus the resulting common blowups retain the original base.

This replacement is verified through the462-module/1,339-declaration audit
and root build. It permits freezing additional VF parameters without
assuming that the enlarged named base is literally a field. The induction
for several-coordinate6.14 is still in progress.


### Section 6: the contraction induction with finite selected volumes

The full6.14 and relative6.15 proofs use actual head preparations. Freezing
the complementary VF tuple gives a unary Gamma bijection followed by its
canonical lift. Its carrier is exactly the lift of the head-contracted RV
fibre. A finite-RV-fibre argument shows that the new RV head value together
with the selected old labels has finite fibres. Unary witness uniformity
therefore compares actual finite head fibres. Induction applies to the
remaining preparations, retaining the head RV value among the selected
coordinates. The recursively ordered final volume has the same weight as
the ordinary contraction volume with the selected old labels appended;
an actual Gamma RV isomorphism connects the presentations.

The487-module/1,397-declaration audit and root build verify the complete
argument. This implements the paper's induction while replacing its
unexpanded compactness and carrier-identification steps with the checked
finite witness coding, exact descent and original-base arguments above.
Whether these details warrant a separate mathematical writeup, beyond the
coefficient-field elimination already recorded, should be assessed in the
final comparison with the printed proof.


### Section 6: coordinate exchange verification

The519-module/1,490-declaration audit and root build verify full6.16.
The proof follows the paper: freeze all remaining VF coordinates, apply
the authorized 5.8 refinement and proved6.15 in two VF coordinates, then
use6.14 for the remaining contractions. Actual partial programs restrict
to the frozen prefix; their unary special witnesses are obtained by
restricting the original ones and extending only internal real
presentations. Exact head-image and volume identities connect the
resulting RV[2] fibres to the original program. These are explicit
implementation details of the printed argument, not currently a separate
replacement proof. The5.8 input produces particular isomorphic
contractions after a VF-preserving refinement and contains no Isp premise.


### Section 6: canonical comparison for contraction objects (verified)

The560-module/1,596-full-audit boundary establishes that canonical
identity-head contraction programs on an RV-pullback fix VF and give
mutually contractible natural lift bijections. Their induced maps on RV
keys preserve the complete volume tuple, giving actual Gamma RV
isomorphisms. Arbitrary contraction-order and preparation independence,
proved by the6.14–6.16 argument, then compares every finite standard
contraction with the RV data of the pullback. This supplies an explicit
replacement for relying on the informal assertion that every relative
contraction's natural map is globally special. It uses no new Section 6
hypothesis; only the authorized Section 5.8 input remains. The kernel theorem6.17 using this comparison and the subsequent
integration statements6.18–6.22 are now verified in the 733-module,
2,268-full-type/axiom audit. The final root build and project-wide QE/Sections2–6 audits also pass.

## Section 7 reconstruction candidate

The checked `Integration7.ElementaryBlowupIsomorphism.elementaryBlowupIso`
construction (declaration `IntegrationInACVF.Section7.elementaryBlowupIso`)
identifies the corrected RV Jacobian directly from normalized residue
tangents. Coordinate projection gives the head block; polynomial vanishing
on actual punctured vertical lines gives the last tangent column. Generic
head and full Jacobians are obtained separately, with the dimension of the
head exception controlled through the product chart. This avoids requiring
a pointwise chain rule at exceptional labels. The formal argument is
verified through the fourth and sixth reconstruction batches. Fresh comparison with Lemma7.2 in the v2 paper confirms that the head-block
and vertical-column argument follows its mathematical strategy. The checked
polynomial tangent reasoning fills in its determinant justification; it is
not currently classified as a different proof. Routine chart encoding and
the ordinary four-piece refinement are likewise implementation detail.

The reconstructed proof of Lemma7.4 now includes actual product charts,
all ordinary RV[0] cases, both distributivity laws and the graded semiring
quotient projection. These spell out the paper's formal congruence argument
and are not currently classified as a substantially different mathematical
proof. The direct left-distributivity chart preserves coordinate order; the
separate block-swap argument retains its determinant sign.


The reconstructed uniform Jacobian certificate proof makes explicit the
finite polynomial supports and smaller-dimensional exceptions needed by
the compactness step for7.5. Its generic-cover argument reuses the checked
predecessor's residue charts and full-dimension argument. This is verified
implementation detail; the complete7.5 comparison remains open.


The original-Gamma chart descent is now verified: the real chart operation
is uniform in representative codes, and equal Gamma codes have identical
input rows and hence identical output rows. Essential schema restriction
retains the density and the finite bound. These are implementation details
of the pending compactness argument, not a new proof of7.5.


The finite formula criterion for a fixed essential volume chart is now
verified in both directions. Gamma weight is encoded by the actual RV
coordinate product times density, using equality of valuations. A finite
polynomial chart certificate handles the RV equation outside its explicit
small-dimensional exception. This prepares the pending7.5 compactness step
and is not a completed replacement proof of that lemma.


The bounded exception can now be coded on the actual coordinate-and-density
label space: the finite weight map images the original small exception,
and its finite pullback proves soundness. The original-Gamma first-order
validity locus for the resulting volume-isomorphism schema is checked.
Realization/promotion and the7.5 compactness/gluing argument remain open;
this is still verified implementation detail rather than a completed
replacement proof of7.5.


Valid original-Gamma volume-isomorphism schema rows now realize actual
volume isomorphisms. The proof reconstructs the essential chart from its
bijectivity formula, derives the actual correspondence from the coordinate
graphs, interprets the density ratio exactly, and bounds the exception by
its finite map. A finite internal code extension retains the full original
Gamma chart, without a generation claim. This is checked implementation of
the pending compactness step; witness promotion and7.5 are still open.


Volume-object promotion now preserves full original-Gamma coordinate and
density graphs exactly. Auxiliary names may occur in a finite exception
certificate and are existentially quantified in its first-order validity;
the geometric objects and comparison chart remain independent of them.
Soundness reconstructs an actual volume isomorphism with that fixed chart.
This checked implementation does not assume a Gamma-definable choice of
exception map or auxiliary names. Complete comparison-witness promotion
and the7.5 common-blowup comparison remain unfinished.


Comparison promotion is now checked for an internal context explicitly
presented as the term closure of the original real base and named tuples.
Raw singleton parameter elimination descends the actual exception-map
formulas to those generators; its auxiliary tuple is then existentially
hidden. The comparison chart retains its full original-Gamma certificate,
and both endpoint schemata can be fixed exactly. This is implementation of
the pending witness-compactness argument, not a completed proof of7.5.


Coproduct and elementary-blowup volume formula operations now retain the
actual density and have proved function validity. Native finite objects
provide the coordinate bounds, with original-Gamma admissibility explicit
for the elementary construction. Full coordinate/density row equality
makes the blowup-witness validity first order. The witness realization,
promotion and compactness/gluing argument remain unfinished; these are
checked implementation details of the intended7.5 proof.


Section7 reconstruction update: sound geometric realization of the finite
volume-blowup witness is checked in the264-module/1,046-export boundary.
Normalization preserves literal tags, cone membership and the elementary
coordinate program; the pulled-back density and exact comparison graphs
match the formula data. This is explicit encoding and semantic transport,
not a new mathematical replacement proof. Full witness promotion, compactness/
gluing and positive selected7.5 remain open. The new19 exports passed the
342-line incremental audit and10,316-job affected Library build.


Section7 update: the274-module/1,072-export boundary checks original-base
promotion and sound realization of full volume common-blowup witnesses,
then finite-witness compactness with uniform exact-length bounds. The
argument eliminates term-closure parameters and uses the checked native
Gamma compactness theorem. This is an explicit implementation of the
paper's finite-witness strategy, not yet a distinct replacement proof.
Indexed volume gluing and positive selected7.5 are still open. The26 new
exports passed the540-line incremental audit and10,328-job Library build.


Section7 update: the288-module/1,109-export local boundary checks tangent
transport under polynomial maps, the block triangular fixed-head fibre
Jacobian comparison, and the RV base-plus-fibre dimension bound via
coordinate bases and algebraic parameter elimination. These supply the
explicit volume-gluing argument under construction. Assess any substantive
proof difference after the complete7.5 proof is established; it remains
open. Joint volume objects, exact fibre semantics and the underlying
joint comparison bijection are also checked. The37 new exports passed the
652-line incremental audit and10,354-job affected Library build.


## Indexed volume equations

The twenty-sixth batch proves `indexedVolumeIso`: a uniformly valid
original-Gamma volume certificate gives the actual indexed volume
isomorphism once its underlying chart is interpreted. The Gamma equation
holds at every essential label. For the RV equation, a definable generic
Jacobian is compared with the definable density ratio. On each fixed-index
fibre, disagreement is contained in an actual local volume exception in
a small containing context. Parameter invariance descends that dimension
bound; the base-plus-fibre bound makes the global disagreement smaller
than the joint volume degree. No definable choice of additional fibre
parameters and no global definability of the Jacobian predicate is assumed.

The 11-module/29-export batch passed its full 846-line type/axiom review
and the 10,365-job affected Library build. The checked local boundary is
299 modules plus Library, with 1,138 audited exports. Indexed blowup and
common-witness gluing, selected-family specialization and positive selected
Lemma 7.5 remain open. The next GitHub backup remains near 364 modules.


## Indexed forward volume blowups

The twenty-seventh batch realizes joint original-Gamma volume charts
in finite containing contexts and transfers them between arbitrary
presentations of equal full rows. Indexed assembly commutes with actual
coproducts and elementary volume blowups: the complete coordinate tuples
and scalar densities are preserved. Uniform fibre admissibility gives
actual last-coordinate admissibility in the joint object. Bound-independent
finite row maps and functional density graphs supply all derived indexed
presentations.

`GammaRVVolumeBlowupSchema.indexedRealize` constructs a genuine forward
volume blowup. `GammaVolumeChainSchema.indexedRealize` and
`GammaVolumeCommonSchema.indexedRealize` retain the exact chain lengths
and the actual terminal volume comparison. Their conclusion is over a
finite containing context; no field or VF/Gamma generation assertion is
added. The index set may be infinite.

The 16-module/28-export batch passed the complete 734-line type/axiom
review and the 10,393-job affected Library build. The checked local boundary
is 315 modules plus Library, with 1,166 audited exports. Finite-cover
partition gluing and the selected-family specialization of positive
Lemma 7.5 remain open. The next GitHub backup remains near 364 modules.


## Finite volume-witness gluing and exact parameter transport

The twenty-eighth batch glues a finite cover by original-Gamma volume
witnesses over an actual RV base. Definable binary partitions and the empty
index case are included. The result consists of actual common forward
volume blowups in a finite containing context.

Named-context promotion now retains zero extra parameters in every
comparison certificate. Compactness supplies a finite cover by such
witnesses. Full raw coordinate and density rows, supported RV Jacobian
formulas, exceptions, admissibility and all internal charts transport
through a parameter recoding. The exact chain lengths are retained.

The 19-module/70-export batch passed its complete 1,152-line type/axiom
review and the 10,418-job affected Library build. The checked local boundary
is 334 modules plus Library, with 1,236 audited exports. VF preparation and
the selected-family specialization of positive Lemma 7.5 remain open.
The next GitHub backup remains near 364 modules.


## VF preparation and actual focus volume blowups

The twenty-ninth batch codes all primitive coordinate, density, exception
and witness formulas by finite RV tuples, prepares them simultaneously
on the VF base, and descends their exact rows to RV keys. The finite
indexed gluing theorem then gives actual common forward volume blowups.
`selected_family_volume_preparation` obtains these data from the concrete
selected-family fibre hypothesis. Its endpoint bounds are proved by
compactness, and adjoining the density graph is an actual fibre volume
isomorphism. The VF field assumption remains on the original base.

The contraction-side construction now includes canonical volume labels,
full-focus elementary volume blowups, literal pullback presentations and
partitions preserving every volume coordinate and the density. The active
locus of an arbitrary last-coordinate focus is proved admissible.
`partialFocusVolumeBlowup` assembles the active elementary blowup and the
unchanged complement into one genuine volume blowup. No geometric
comparison is assumed in its conclusion.

The 26-module/82-export batch passed the complete 1,635-line type/axiom
review and the 10,451-job affected Library build. The checked local boundary
is 360 modules plus Library, with 1,318 audited exports. Iteration along
special chains, comparison with arbitrary same-order contractions, and
the final positive selected Lemma 7.5 remain open. The next GitHub backup
remains near 364 modules; no smaller remote checkpoint was published.


## Unary special-chain volume iteration

`unary_special_volume_chain_pair` and `corollary_6_10_unary_volume`
iterate actual volume blowups through unary special bijections. The number
of blowups is the chain length, and the terminal comparison is an actual
RV volume isomorphism with the canonical pullback object. The density is
retained as an old RV label. `rvVolumeDensityGraphIso` supplies that label
for an arbitrary positive RV volume object without changing its degree.
The required small parameter context is explicit; no VF field or Gamma
generation hypothesis is introduced on temporary contexts.

The four-module/13-export batch passed the complete 253-line type/axiom
review and the 10,455-job affected Library build. The checked boundary is
364 modules plus Library, with 1,331 audited exports. The unary comparison
of two different special preparations, arbitrary same-order contractions,
and the final positive selected Lemma 7.5 remain open. This boundary is
the next authorized backup, 100 modules after the 264-module checkpoint.
GitHub Actions run43591052527 completed successfully for the earlier
252-module revision; it does not certify this newer boundary.
