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


## Unary volume common blowups

`corollary_6_11_unary_volume_presented` constructs actual common forward
volume blowups from a unary volume-preserving lift with its full original
Gamma graph. Its source objects have literal finite-volume presentations
and densities recorded as old RV labels. Both compatible special
preparations are constructed in a genuine small containing context.
The terminal RV volume isomorphism follows from the actual conjugated
volume equation and the checked lift descent. The finite family of extra
Gamma representatives is tracked explicitly; temporary contexts carry
no additional VF-field or generation assumption.

The 13-module/28-export batch passed the complete 684-line type/axiom
review and the 10,778-job affected Library build. The checked boundary is
377 modules plus Library, with 1,359 audited exports. The remaining work
for Lemma 7.5 is to pass from unary slices to arbitrary standard
contractions and complete the ordered head induction. Later Section 7
statements also remain open.

The authorized 364-module/1,331-export backup was published as
`dfcd19415d6ea7ba4c4cbaaec75277d1ae8a9064` on
`section-7/reconstructed-foundation`; all 439 file blob hashes, its parent,
tree, branch head and unchanged main revision were verified. The local
source archives were reopened and byte-verified at that boundary. The
next backup remains near 464 modules; this batch adds no remote push.


## RV slice densities and promotion in containing contexts

The thirty-second batch constructs RV-prefix slice volume schemata with
retained density labels, proves a uniform valid bound for every slice,
and constructs `gammaVolumeSliceDensityAssemblyIso` preserving the full
coordinate tuple and density. Given original-Gamma common formula
witnesses on every slice, `gamma_volume_slice_density_common_uniformity`
constructs the presentations and containing contexts and gives actual
common forward blowups of the original objects.

`finite_auxiliary_map_promotion_free` extracts finite sorted parameters
from a genuine exception map in any real context. Consequently
`gamma_volume_row_comparison_promotion_free` needs no equation identifying
the whole context with the named term closure. Its full original-Gamma
chart remains an explicit input. Object promotion likewise works from
its exact original-Gamma domain, coordinate and density graphs.

The eight-module/15-export batch passed its complete 360-line type/axiom
review and the 10,791-job affected Library build. The checked boundary is
385 modules plus Library, with 1,374 audited exports. To apply the slice
uniformity theorem to the unary preparation proof, its actual focus
chains must still supply original-Gamma formula witnesses. This has not
been assumed or counted as established. Arbitrary same-order standard
contractions, the positive selected Lemma 7.5 and later statements remain
open. The next authorized GitHub backup remains near 464 modules.


## Original-Gamma volume chart interfaces

The thirty-third batch proves the full original-Gamma graph for retained
coordinate densities, canonical native objects, essential domains and
canonical coordinate-and-density preserving isomorphisms. These graphs
are closed under composition and inverse. Original-Gamma admissibility
transfers to a promoted schema row while retaining the original algebraicity
base. `gamma_volume_blowup_row_promotion` constructs a formula witness
from canonical blowup endpoint charts with those full Gamma graphs,
without requiring the containing real context to equal the named closure.

The six-module/13-export batch passed its complete 360-line type/axiom
review and the 10,797-job affected Library build. The checked boundary is
391 modules plus Library, with 1,387 audited exports. Instantiating these
interfaces on the actual partial-focus chains, producing their formula
witnesses and finishing arbitrary contraction comparison remain open.
The final positive selected Lemma 7.5 is still in progress. The next
GitHub backup remains near 464 modules.


## Original-Gamma partial-focus volume witnesses

The thirty-fourth batch constructs full and partial focus volume charts
over the original Gamma base. Canonical transport commutes with the
actual elementary object, using the proper RV multiplication formula.
The full-focus chart and unchanged-complement chart preserve every
coordinate and the retained density. Their coproduct and pullback partition
charts remain original-Gamma definable. Finally,
`gamma_partial_focus_volume_schema` constructs a genuine finite volume
blowup formula witness in an arbitrary containing real context. No equality
between that context and the original named closure is assumed.

The 13-module/23-export batch passed its complete 619-line type/axiom
review and the 10,837-job affected Library build. The checked boundary is
404 modules plus Library, with 1,410 audited exports. Chain induction,
unary family witness gluing and arbitrary contraction comparison remain
open; positive selected Lemma 7.5 is still in progress. The next GitHub
backup remains near 464 modules.


## Unary common-volume-blowup formula witnesses

The thirty-fifth batch proves `gamma_unary_special_volume_schema_pair`
for complete alternating unary special chains, including canonical steps
absorbed into source charts. `gamma_unary_volume_common_schema` combines
two actual volume-preserving preparations and the original-Gamma terminal
comparison into a finite common-blowup formula witness. The containing
context may have extra internal real codes; its VF-field generation is
not assumed. VF-fixed, density-preserving Gamma lift comparisons are
realized in genuine small contexts and glue across all RV-prefix slices.

The eight-module/10-export batch passed its complete 544-line type/axiom
review and the 10,850-job affected Library build. The checked boundary is
412 modules plus Library, with 1,420 audited exports. Arbitrary standard
contraction natural maps can change VF coordinates, so their actual
Jacobian-one/volume comparison still has to be connected to this slice
argument. The ordered head induction and full positive selected Lemma 7.5
remain open. The next GitHub backup remains near 464 modules.


## Natural unary contraction volume maps

The thirty-sixth batch proves that an actual VF-arity-one relatively
special map is a special bijection over the original real base. Therefore
every arbitrary unary ordered/standard contraction natural map has VF
Jacobian one almost everywhere. Its normalized lift bijection preserves
the transported volume form, whose retained density remains the original
old-label coordinate. The mixed Jacobian is unchanged by altering only
output RV labels. Finite-fibre pullback and composition control exceptions
on prepared RV families, and their explicit VF-base projections are
constructed and proved finite-to-one.

The exact original-Gamma point formulas of selected-contraction and
prepared-family slice lift charts are checked. Their small-context
realizations preserve volume whenever their VF components follow the
checked Jacobian-one maps. `gamma_unary_common_from_lift_charts` combines
two such charts, allowing the VF coordinates to move, into a finite
common-volume-blowup formula witness over the original Gamma base.

The 11-module/28-export batch passed its complete 707-line type/axiom
review and the 10,897-job affected Library build. The checked boundary is
423 modules plus Library, with 1,448 audited exports. Instantiating these
interfaces on the prepared selected slices and the subsequent ordered
head induction remain open; positive selected Lemma 7.5 is not complete.
The next GitHub backup remains near 464 modules.


## Unary prepared selected-volume comparison

The thirty-seventh batch constructs actual small-context selected slices,
verifies their contraction and preparation VF charts, and applies the
unary common-witness theorem on every RV-prefix slice. Uniform gluing
proves `gamma_unary_prepared_volume_comparison` for an arbitrary unary
standard contraction and its prepared indexed family. The starting
containing context is arbitrary, so successive comparisons can be
composed without merging unrelated small bases.

Prepared indexed presentations retain the exact old density label.
The canonical coordinate-density realization is genuinely volume
isomorphic to that full indexed presentation. Applying the same volume
coordinate permutation to both sides preserves common blowups: its
determinant signs are explicitly canceled by simultaneous rescaling.

The 11-module/20-export batch passed compilation, full 643-line
type/axiom review and the 10,908-job affected Library build. The checked
boundary is 434 modules plus Library, with 1,468 audited exports.
The two-family unary composition and subsequent ordered head induction
remain outside this checked boundary. Positive selected Lemma 7.5 is
not complete. The next GitHub backup remains near 464 modules.


## Unary selected families and arbitrary parameter bases

`gamma_unary_fibrewise_volume_comparison` composes the two arbitrary
unary contraction comparisons through one prepared family.
`selected_unary_volume_comparison` instantiates it on actual selected
volume families and their density graphs, using only the original
fibrewise common-blowup hypothesis, the stated field/base conditions,
and arbitrary unary standard contractions. Its conclusion is an actual
common blowup in a containing context, with selected coordinates first.
Restoring the full ordered target and proving the head induction remain
separate obligations.

`unary_bijection_preparation_in_context_without_field` names the
generated coefficient field inside a genuine small context, applies
checked preparation, and eliminates those names from every resulting
chain and graph. Thus `gamma_unary_volume_common_schema_without_field`
and the moving unary lift/slice/prepared comparisons require no VF-field
hypothesis on frozen parameters. Witness formula base changes preserve
all full rows, exceptional auxiliary arities, validity and exact chain
lengths. The finite volume-witness cover can also be prepared over an
arbitrary small real base under uncountable saturation.

The 10-module/31-export batch passed compilation, complete 1,060-line
type/axiom review and the 10,981-job affected Library build. The checked
boundary is 444 modules plus Library, with 1,499 audited exports.
Positive selected Lemma 7.5 is still open: the general head induction
must retain original-base geometric witness data through uniform gluing.
The next authorized GitHub backup remains near 464 modules.


## Original-Gamma Jacobian and correction graphs

The 20-module/46-export batch proves parameter extension for actual
standard contractions, preserving their chosen maps and volume indices.
`selected_unary_volume_comparison_without_field` compares arbitrary
unary contractions of actual selected density-graph families under the
original fibrewise common-blowup premise, without a coefficient-field
hypothesis. The conclusion lives in a genuine containing small context;
it does not assert common witnesses over the original named context.

Generic RV Jacobians, including supported-chart fallback values, now
have graphs definable over the original real/Gamma parameter base.
The same holds for the head Jacobian after an elementary blowup, its
unit-normalized correction and the packed nonzero cone-fibre map.
The exceptional small set in the generic Jacobian theorem is not
claimed Gamma-definable. These are inputs toward Gamma-preserving
elementary comparison and ordered induction, which remain unfinished.

The source batch compiled, its full 1,235-line type/axiom report was
reviewed, and the affected Library build passed (11,002 jobs including
cached dependencies). The checked boundary is 464 source modules plus
Library and 1,545 audited exports. This is the next authorized backup
boundary, 100 modules beyond the last published proof checkpoint.


## Original-Gamma elementary comparison

`VolumeObjectGamma.elementary_comparison` proves actual volume
isomorphism of canonical elementary blowups, retaining the original
Gamma graph. It applies directly to actual objects with full Gamma
coordinate and density graphs and ordinary admissible centers.
`exists_gamma_elementaryBlowupIso` also handles arbitrary elementary
charts whose packed essential maps have full Gamma graphs. The proof
chooses the checked Gamma head Jacobian and uses the actual corrected
map and the already proved almost-everywhere volume Jacobian equation.

The coordinate, density and packed-chart graphs of canonical elementary
blowups follow directly from those of the original actual object.
Restrictions, inverse maps and tagged coproducts preserve their full
graphs. This removes a presentation-change obstacle in the pending
Gamma refinement argument. No new Gamma algebraicity is inferred from
ordinary admissibility, and this batch does not finish Lemma 7.5.

The 14-module/28-export batch passed source compilation, full type/axiom
review, explicit existential endpoint-type inspection and the affected
Library build (11,016 jobs including cached dependencies). The checked
boundary is 478 modules plus Library, with 1,573 audited exports.
The 464-module checkpoint was uploaded as commit
81636ccb0409fe4eb5e3557255c5aa1065c9ca5a; all 557 remote blob identities,
its ancestry and branch ref were checked. Main was unchanged. CI was
running at publication. Two local recovery archives were reopened and
byte-verified at the same 464-module boundary.


## Original-Gamma geometric common refinements

`gamma_volume_blowup_diamond` constructs a genuine square of actual
volume blowups, retaining full original-Gamma charts on both new steps
and their endpoint isomorphism. Full elementary charts include degenerate
labels. The original-base center algebraicity, encoded by
`GammaBlowupCenter`, passes to the two new restricted centers.

`GammaIteratedVolumeBlowup.common_refinement_of_iso` applies the already
checked finite-grid argument to Gamma volume-isomorphism classes and
realizes actual chains with the exact two opposite lengths.
`GammaVolumeBlowupEquivalent.trans` composes common refinements while
retaining original-Gamma geometric data. No quotient-class permutation
is used to select an unchecked comparison chart.

`gamma_charted_volume_common_promotion` converts these geometric
witnesses into valid common-witness formulas in any genuine containing
context. Center admissibility remains over the original real/Gamma base.
The exceptional-set certificates still have explicit auxiliary parameters;
the theorem does not claim `NoAuxiliary` or a named-context equality.
Preparing such general certificates and the ordered head induction for
positive selected Lemma 7.5 remain unfinished.

The 25-module/75-export batch passed source compilation, complete
1,390-line type/axiom review (including explicit existential endpoint
types and the new structure/inductive constructors), and the affected
Library build (11,041 jobs including cached dependencies). The checked
boundary is 503 modules plus Library, with 1,648 audited exports.
The next GitHub backup remains near 564 modules.


## Preparation with general auxiliary exception certificates

`certificateWithFrozenParameters_valid` removes the auxiliary-free
restriction from certificate recoding. The geometric source, target,
coordinate/density rows and comparison chart descend to the prepared
RV key. The old parameter tuple is retained existentially inside the
exception certificate, alongside its original auxiliary tuple. A new
ignored prefix makes that same finite exception map a valid witness at
the new key. No old parameters are added to the fixed base or to the
geometric labels. The actual exceptional row, its finite-fibre bound,
chart supports, exception degree and exact blowup lengths are retained.

`commonWithFrozenParameters_valid` extends this construction through
complete common-witness formulas. Only their geometric primitive rows
need finite VF codes. Thus `prepare_volume_geometry_cover_in_context`
and `volume_formula_prepared_common_uniformity_in_context` prepare and
glue arbitrary finite formula-witness covers in genuine small contexts.
Neither a coefficient-field hypothesis, `NoAuxiliary`, nor equality
with a named term context is required.

`gamma_geometric_prepared_volume_uniformity` applies this to original-
Gamma geometric common refinements in arbitrary contexts.
`gamma_unary_volume_comparison_from_formula_witnesses` compares arbitrary
unary standard contractions from general formula witnesses, preserving
the original chosen contraction objects and retained densities. Its
conclusion is actual common blowup equivalence in a containing context;
full Gamma indexed realization and the ordered head induction for
positive selected Lemma 7.5 remain unfinished.

This is a verified replacement for the earlier auxiliary-free coding
shortcut: it avoids any need to code arbitrary auxiliary VF parameters
by RV parameters or choose their values uniformly.

The 12-module/37-export batch passed source compilation, complete
979-line type/axiom review (with explicit endpoint types and the recoding
definition), and the affected Library build (11,053 jobs including cached
dependencies). The checked boundary is 515 modules plus Library, with
1,685 audited exports. The next GitHub backup remains near 564 modules.


## Gamma indexed realization and unary preparation

General common-witness formulas now realize indexed elementary blowups,
finite chains and finite-cover common refinements with full original-Gamma
coordinate, density and comparison graphs. Center algebraicity remains
over the original real/Gamma base. Coproducts and finite partition gluing
retain this geometry; arbitrary auxiliary exception parameters are allowed.

`HasPreparedGammaVolumeCommonComparison` records the strengthened prepared
family conclusion. `volume_formula_prepared_gamma_uniformity_in_context`
constructs it from pointwise general formula witnesses in genuine small
contexts. `gamma_unary_prepared_volume_comparison_with_geometry` compares
an arbitrary chosen unary contraction with the prepared family using
actual Gamma common blowups. Gamma block-swap composition and the ordered
head induction for positive selected Lemma 7.5 remain unfinished.

The 21-module/38-export batch passed actual source compilation, complete
1,057-line type/axiom review, including the prepared comparison definition,
and the affected Library build (11,074 jobs including cached dependencies).
The checked boundary is 536 modules plus Library, with 1,723 audited exports.
The next GitHub backup remains near 564 modules.


## Unary comparison with original-Gamma geometry

`gamma_unary_volume_comparison_with_geometry` strengthens the unary
positive selected-volume comparison to actual common blowup chains with
full original-Gamma geometry, from arbitrary valid formula witnesses.
It preserves the original chosen contractions through parameter enlargement.
No auxiliary-free restriction or coefficient-field premise is added.

Simultaneous coordinate permutations preserve Gamma common blowups by
correcting their common determinant sign with an original-base term
constant. Term-closure parameter elimination shows this constant adds
no parameters to the original Gamma graph. Density rescaling, degree
reindexing, block swapping and the actual coordinate-density assembly
charts retain the geometric witnesses and center algebraicity.

The 9-module/19-export batch passed actual source compilation, complete
695-line type/axiom review and the affected Library build (11,083 jobs
including cached dependencies). The checked boundary is 545 modules plus
Library, with 1,742 audited exports. Higher-dimensional ordered head
induction for positive selected Lemma 7.5 remains unfinished.
The next GitHub backup remains near 564 modules.


## Actual frozen head fibres and their unary comparisons

`headCoordinateFibrePreparation` restricts an actual head preparation to a
genuine unary head preparation, and `headCoordinateFibreContraction` makes
it an actual unary standard contraction. Their original-Gamma graphs name
exactly the complementary VF tuple. `head_fibre_raw_volume_equivalence`
identifies their raw RV output with the original head-contracted fibre,
preserving the full selected volume tuple and all labels. The induction
interface retains old selected coordinates first, then appends the new
head tag; selected finiteness and the retained density are proved.

`unary_selected_normalization_volume_iso` realizes the raw-to-normalized
comparison as an actual Gamma volume isomorphism, preserving the selected
volume coordinates and density. `selected_coordinate_density_schema_row`
identifies arbitrary selected finite presentations with their full volume
schema rows. `selected_volume_head_formula_witnesses` specializes the
original pointwise geometric hypothesis to valid unary witnesses after
freezing the tail. Equal-base and row transport preserve geometric data.

`volume_common_gamma_in_term_context` supplies original-Gamma geometry
for ordinary common witnesses in an actual term-generated named context;
center algebraicity descends by term parameter elimination. No statement
identifies a general containing context with that term closure.

The head common-refinement composition and higher-dimensional ordered
induction for positive selected Lemma 7.5 remain unfinished.

The 19-module/44-export batch passed actual source compilation, complete
881-line type/axiom review and the affected Library build (11,112 jobs
including cached dependencies). The checked boundary is 564 modules plus
Library, with 1,786 audited exports. This is the next 100-module backup
boundary after the published 464-module checkpoint.


## Positive selected Lemma 7.5: arbitrary dimension

`lemma_7_5_positive` proves the positive-selected-degree comparison for
arbitrary actual standard contractions in a common order, starting from
the ordinary common-blowup hypothesis on the actual named VF fibres.
The head comparison is composed from genuine frozen unary contractions,
full raw coordinate equivalences, and actual original-Gamma common chains.
The resulting ordered induction has no additional head comparison premise.

The conclusion realizes the full coordinate and density rows of the
chosen contraction targets by actual original-Gamma volume objects and
common blowup chains. `standard_append_volume_index_closed` identifies
the coordinates as the old selected coordinates followed by every VF tag
in the common contraction order; `standard_append_density_index` retains
the original density. This batch does not identify these presentations
with the older object frontend whose VF tags were reversed.

The 14-module/29-export batch passed actual source compilation, one full
891-line type/axiom review and the affected Library build (11,126 jobs
including cached dependencies). The checked boundary is 578 modules plus
Library, with 1,815 audited exports. Corollary 7.6 and subsequent results
remain unfinished. The next requested backup boundary is about 664 modules.


## Unary Corollary 7.6 and actual fibre Jacobians

`gamma_unary_contraction_volume_comparison` constructs actual original-
Gamma common volume blowup chains for arbitrary chosen unary standard
contractions of measure-preservingly isomorphic mixed sets with finite
RV fibres. The measure hypothesis is the existing almost-everywhere VF
volume equation. Conjugacy transports the actual forms; zero-prefix
row semantics and the checked witness gluing give the actual chains.
The original density is retained on the whole RV domain.

`relative_mixed_vf_jacobian_on_coordinate_fibre` proves pointwise that
a defined full mixed VF Jacobian of a relatively unary map equals the
unary Jacobian on its actual fibre. It constructs the restricted chart,
including source membership and the fixed output RV labels. The matrix
proof identifies all other rows with the identity and computes the
active diagonal determinant. `relative_volume_on_fibre_of_small_exception`
transfers the measure equation when the witnessed exception intersects
that fibre in a VF-small set. It does not assert that this holds on every
fibre from a global almost-everywhere hypothesis. The arbitrary-dimensional
exception comparison in Corollary 7.6 remains unfinished.

The 8-module/16-export batch passed actual source compilation, one full
459-line type/axiom review and the affected Library build (11,134 jobs
including cached dependencies). The checked boundary is 586 modules plus
Library, with 1,831 audited exports. No repeated earlier integrity audit
was performed. The next requested backup boundary remains about 664 modules.


## Lemma 7.5 completed in the accepted scope

`lemma_7_5` proves the nonempty-selected-coordinate statement on the
specified actual contraction objects. Its input is the ordinary common-
blowup hypothesis on the actual named fibres only on the common VF
projection. Empty fibres outside that projection compare directly. Its
output supplies actual original-Gamma common forward blowup chains in an
internally constructed containing context. `lemma_7_5_ordinary` forgets the
extra Gamma certificates and returns the usual common-blowup relation.

`standardAppendVolumeObject` retains the complete RV labels, every old
selected coordinate, all contracted VF tags in the common order, and the
original density. Its finiteness and nonvanishing are proved. Equal full
coordinate/density rows are compared by an actual Gamma volume chart;
`commonByGammaGeometry_on_objects` joins the containing contexts and
transfers the actual chains to these specified objects. This closes the
row-to-object interface left open in the preceding batch. The E-empty
case remains outside the user-approved target.

The 7-module/14-export batch passed actual source compilation, one full
346-line type/axiom review and the affected Library build (11,141 jobs
including cached dependencies). The checked boundary is 593 modules plus
Library, with 1,845 audited exports. The arbitrary-dimensional version of
Corollary 7.6 and 7.7-7.15 remain unfinished. Backup remains due at about
664 modules, as requested.


## Arbitrary forms in unary 7.6 and VF-small contractions

`corollary_7_6_unary` proves the unary result for arbitrary original VF
volume forms, actual volume-preserving bijections and specified actual
density-graph contractions. The original-Gamma common chains retain the
original density. Native map realization uses the shared language and
actual raw-point presentations, preserving point values and bijectivity.

`PositiveVFVolumeObject.standardContractionObject` constructs the actual
standard contraction object in every positive degree with proved full
Gamma graphs and retained nonzero density. The actual natural lift map
is bijective and preserves VF dimension; no higher-dimensional Jacobian
claim is included in that interface. A nonempty essential RV object lifts
to full VF dimension, so any chosen contraction of a VF-small object has
empty essential domain. Such objects compare by a genuine original-Gamma
volume isomorphism, independently of contraction order. This establishes
the lower-dimensional case needed for the remaining exception argument.

The 8-module/18-export batch passed actual source compilation, one full
316-line type/axiom review and the affected Library build (11,149 jobs
including cached dependencies). The checked boundary is 601 modules plus
Library, with 1,863 audited exports. General full-dimensional Corollary 7.6
and 7.7-7.15 remain unfinished. Backup remains due at about 664 modules.


## Relative heads and essential base indices

Actual chosen head contractions now compare on every frozen fibre on which
one witnessed global measure exception has VF dimension below one. Raw
and normalized finite contraction objects are related by actual original-Gamma
volume isomorphisms, including the first-head case with no old selected
coordinates. Indexed uniformity now needs witnesses only on indices whose
base volume coordinates are all nonzero; the other indices are discarded
through proved volume isomorphisms containing the entire essential domain.

The ordered relative comparison under measure preservation on every fibre
is a conditional support theorem. It is not counted as general Corollary
7.6, whose exceptional-base argument remains active. The 12-module and
17-export batch passed actual compilation, one full 773-line type/axiom
review and the affected Library build (11,163 jobs including cached
dependencies). The checked boundary is 613 modules plus Library, with
1,880 audited exports. General higher-dimensional 7.6 and 7.7-7.15 remain
unfinished. Backup remains due at about 664 modules.


## Corollary 7.6 completed in all positive dimensions

`corollary_7_6` compares the actual specified density-graph standard
contraction objects of arbitrary original volume forms. The full VF
bijection is relatively unary in the first coordinate of the chosen
common order, and only the original global almost-everywhere volume
equation is required. The output consists of actual original-Gamma
common forward blowup chains in a genuine containing context.

The exceptional-fibre argument now proceeds through generic points:
a VF-small global exception has small unary fibres at independent base
tuples; compactness supplies finitely many witnesses covering all such
tuples; every nonzero prepared RV cell has a generic inverse image.
Essential-index gluing then compares the whole prepared objects. A
positive-selected contraction induction valid at generic parameters
extends the head comparison through every remaining specified step.
Simultaneous VF permutations retain the actual mixed Jacobian, and the
corresponding RV coordinate permutations retain common blowup geometry
with unchanged densities. No all-fibres measure premise, new Section 5.8
input or generation hypothesis has been added to Corollary 7.6.

The 30-module/43-export batch passed actual compilation, one full
1,832-line type/axiom review and the affected Library build (11,194 jobs
including cached dependencies). The checked boundary is 643 modules plus
Library and 1,923 audited exports. The next active target is 7.7; 7.7-7.15
remain unfinished. Backup remains due at about 664 modules.


## Balanced-cell translation milestone for 7.7

Both translations are actual native definable bijections onto the
paper’s two product domains. Their centres and complete map graphs retain
the original real/Gamma base. They have mixed VF Jacobian one almost
everywhere; pure VF domains with arbitrary transported original densities
give actual full volume-preserving bijections. The balanced positioning
function and its inverse have graphs over that same base. The Gamma
product identity follows from the checked slope formula of Remark4.6.

Original VF-independent tuples remain independent after adjoining real
codes for the original Gamma names and taking the substructure closure:
the generated VF field lies in the original algebraic closure. Relative
contraction comparison is proved in those contexts over the unchanged
original base, on actual specified normalized contraction objects.

The 21-module/65-export batch passed actual compilation, one complete
1,608-line type/axiom review and the affected Library build (11,273 jobs
including cached dependencies). This seals 664 modules plus Library and
1,988 audited exports. Lemma7.7 still needs the balanced RV comparison and
uniform cell-family assembly; 7.7-7.15 remain unfinished. The last 564-module
backup passed GitHub Actions run43622491340. The next backup is due at
about764 modules after saving this milestone.


## Balanced unary RV volume comparison for 7.7

`balanced_cell_unary_volume_preparation` constructs the actual unary
projection bijection of a balanced native two-cell, compatible special
preparations from the checked Lemma5.2, finite RV volume fibres, and an
original-Gamma volume isomorphism between the two resulting product RV
objects at every common nonzero constant density. Its existence scope
keeps Lemma5.2’s VFFieldBase hypothesis, actual saturation and original-base
smallness, a real presentation of the positioning graph, and the named
nonzero paradigms. No two-cell comparison theorem is assumed.

The prepared unary coordinate values are related by the original slope.
Mutual contractibility identifies the inverse-special fibres as actual
open balls; the realized difference cuts determine their radii exactly.
Remark4.6 then gives equality of the products of the two Gamma volume
coordinates. A finite RV[2] object with one constant coordinate has RV
dimension at most1, so the RV Jacobian condition is vacuous in degree2.
The constructed isomorphism retains its complete original-Gamma graph.

The 14-module/41-export batch passed actual compilation, one complete
1,206-line type/axiom review and the affected Library build (11,288 jobs
including cached dependencies). The checked boundary is678 modules plus
Library and2,029 audited exports. Lemma7.7 still needs identification with
the specified two-coordinate contractions and uniform4.8 cell-family
assembly; 7.7-7.15 remain unfinished. The durable backup is the664-module
checkpoint46570a319f7bb9a44a53abed2377eca674fefd79; its CI run43633648775
was in progress when published. The next backup remains due at about764
modules, following the author’s100-module preference.


## Actual fixed-label product contractions for 7.7

The eighteenth new module in this batch completes `rv_class_product_standard_volume_preparation`: a supplied actual Gamma unary special with an RV-pullback target constructs an actual two-coordinate standard contraction of an RV-class product, retaining every fixed old RV label. The raw RV object of that contraction is exactly coordinate-preserving and volume-isomorphic to the product of the lifted unary pullback object with the fixed class coordinate, at every common nonzero constant density. The complete graph stays over the original Gamma base. Target finite volume is derived from source finite RV fibres and actual Gamma bijectivity.

The fixed-label focus and chain lifts prove the commuting projection, carried labels, joint determination, exact target carrier, and RV-pullback property. Their projections to the original unary targets are actual Gamma bijections, mutually contractible, and induce actual RV isomorphisms preserving the unary volume coordinate. The standard raw label domain and both volume selectors are identified explicitly. An ordinary isomorphism from the normalized finite RV object is also checked.

This is a product construction, not the full two-order lemma. Joining the fixed-head volume lift of the projection to the original unary targets, essential-domain and density-graph identifications, normalized volume objects, the opposite order and uniform4.8 cell-family assembly remain. Lemma7.5 and Corollary7.6 retain their previous completed scopes;7.7-7.15 remain unfinished.

The18-module/85-export batch passed actual source compilation, one full1,702-line type/axiom review and the affected Library build (11,306 jobs including cached dependencies). The checked boundary is696 modules plus Library and2,114 audited exports. The next remote backup remains due around764 modules, following the author’s100-module preference.


## Balanced translation product comparison over the original base

`balanced_translation_product_volume_comparison` constructs actual opposite-order standard contractions of the horizontal and vertical product images of a native balanced cell. Their actual raw RV volume objects are original-Gamma volume-isomorphic, retaining every fixed old RV label and any common nonzero constant density. The real positioning presentation and actual Gamma centre graphs remain explicit; the latter have already been constructed by the checked translation-centre theorem. No contraction-comparison premise is assumed.

The carried-label preparations project by actual Gamma RV isomorphisms to the original compatible unary targets. These projections preserve the unary volume coordinate; adjoining a fixed head or tail coordinate, essential restriction, and the opposite VF order are now all identified. The balance isomorphism from the prepared unary geometry composes with those actual maps in the same real presentation: the smaller RV dimension makes the RV Jacobian clause vacuous, while the pointwise Gamma equation is proved throughout.

`lemma_5_2_gamma_presented_without_field` uses generated VF field names internally and eliminates them from every actual special-chain certificate and the full conjugate graph. The corresponding balanced unary, product and native product frontends therefore require genuine uncountable saturation and smallness of the original real base, without a VFFieldBase hypothesis. Characteristic00, the named value greater than1, actual balanced geometry, nonzero paradigms, their real presentation names and the fixed-label tuple certificates remain explicit.

Lemma7.7 is not yet complete. The remaining bridges include normalized objects and their retained density-graph forms, comparison with arbitrary specified contractions via Corollary7.6, nonbalanced cells, uniform4.8 cell-family assembly and the higher-dimensional frozen-coordinate reduction. Lemma7.5 and Corollary7.6 retain their completed scopes;7.7-7.15 remain unfinished.

The20-module/50-export batch passed actual source compilation, one full1,833-line type/axiom review and the affected Library build (11,326 jobs including cached dependencies). The checked boundary is716 modules plus Library and2,164 audited exports. The durable backup remains the664-module checkpoint46570a319f7bb9a44a53abed2377eca674fefd79. The next remote backup is still due around764 modules under the author’s100-module preference.


## Normalized balanced translation comparison

`balanced_translation_constructed_common_blowup` compares the actual normalized volume objects of the constructed opposite-order standard contractions on the horizontal and vertical translated images of a native balanced cell. The common blowup uses the proved original-Gamma volume isomorphism. The normalized objects are finite, every old RV label retains its source value, and a selected retained nonzero density coordinate gives exactly the constant-density form used in the comparison. Full original-Gamma endpoint and program certificates are proved. No new comparison or field-base premise is assumed.

This does not complete Lemma7.7: comparisons with arbitrary specified original-cell contractions, nonbalanced cells, uniform4.8 cell-family assembly and higher-dimensional exchange remain open. The11-module/39-export batch passed actual compilation, one full935-line type/axiom review and Library integration (11,337 jobs including cached dependencies). The checked boundary is727 modules plus Library and2,203 exports. The next authorized remote backup remains due around764 modules.


## Arbitrary balanced and degenerate cell contractions

`balanced_cell_opposite_order_contraction_comparison` proves the balanced two-dimensional cell case of Lemma7.7 for arbitrary specified original-Gamma standard contractions in the two opposite orders. It constructs actual common forward blowup chains on their normalized finite volume objects, retaining all fixed old RV labels and the selected nonzero density. `gamma_named_balanced_cell_contraction_comparison` realizes the original Gamma names in a genuine small containing context, constructs the actual translation centres and real positioning presentations, and proves the required preservation of original VF independence internally. Nonzero paradigms and their real presentation names remain explicit. No VFFieldBase premise is added.

The key presentation bridge rebuilds actual Gamma special chains over fixed common names while preserving their point values, focus geometry and alternation. The resulting product programs keep their actual target carriers and volume selectors. Their full original-Gamma volume comparison transfers to that presentation, where Corollary7.6 compares the arbitrary specified original-cell contractions to the constructed product contractions. The retained-coordinate density objects are proved equal to the actual normalized constant-density product objects before composition.

`degenerate_cell_contractions_compare` handles zero-paradigm graph cells and singleton-first-projection cells in any specified contraction orders. The actual natural lift maps preserve VF dimension; these domains have VF dimension at most one, so their degree-two contraction objects have empty essential domains. The resulting volume isomorphism and common chains retain the original Gamma base.

The23-module/55-export batch passed actual source compilation, one full1,400-line type/axiom review and Library integration (11,360 jobs including cached dependencies). The checked local boundary is750 modules plus Library and2,258 exports. No earlier batch was manually reviewed again. Complete Lemma7.7 still needs nonbalanced open rectangles, uniform4.8 cell-family assembly and higher-dimensional exchange;7.7-7.15 remain open. The durable backup remains checkpoint664; the next authorized backup is due around764 modules.


## Rectangle preparations and parameter products

The fifteenth new module in this batch establishes `RVParameterSpecialPreparation.head_product_map_bijective`: the actual contraction of a unary special preparation carrying an arbitrary RV parameter domain is definably bijective to the product of that domain with the original unary contraction. Surjectivity uses the actual special chain and exact source geometry, so no independent amalgamation of potentially overlapping coordinate selectors is assumed. The target pullback and both complete factor maps are proved on the actual label domains.

`nativeUnaryRectangleContraction` builds an actual two-stage standard contraction from the two unary preparations. The first-factor action is proved relatively special by restricting the same unary chain to each frozen-coordinate fibre, including empty fibres; its complete graph retains the original Gamma base. Its first head image is exactly the second unary source over the entire first RV contraction. The second stage carries all these parameters. `gamma_unary_pullback_preparation_over_common_names` produces unary preparations in a specified common-name context without a VFFieldBase hypothesis.

The15-module/50-export batch passed actual compilation, one full798-line type/axiom review and affected Library integration. The checked boundary is765 modules plus Library and2,308 exports. Earlier batches were not manually audited again. The balanced and degenerate cases remain established; the rectangle finite-volume and opposite-order comparisons, uniform4.8 family assembly and higher-dimensional exchange remain to be completed. This is a construction and ordinary output bijection, not yet the full rectangle volume comparison.
