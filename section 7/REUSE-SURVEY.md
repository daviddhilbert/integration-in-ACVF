# Section 7 reconstruction and reuse

The target paper is Yin, arXiv:0809.0473v2, Section 7. Lemma 7.5 has the
user-approved restriction to a nonempty selected coordinate set; see
`TARGETS.md`. Recovery and subsequent reconstruction are separate activities.

The original 1,201-module working copy is unavailable. Sixty complete module
texts were reconstructed from visible conversation commands and remain
preserved in `.scratch/recovery/transcript/Integration7/`. Their manifests
record current hashes, provenance limitations, and verification status.
Newly written prerequisites are not counted as recovered original sources.

## Pinned inputs

- Lean 4.35.0, `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- Special transformations `9cc9760892092dd34cfad4a6dee655843c52f30c`.
- ACVF-QE `939346b0a99899e22a873479364e3cc5d142731c`.

All eleven dependency checkouts passed `scripts/prepare_ci.py`. The
predecessor's language errata and the relevant Section 4 and Section 9
status documents were read before reusing their interfaces. Historical
verification paragraphs under older pins are not new build evidence.

## Algebra

`SemiringGroupification.lean` uses Mathlib's `FreeRing`, `ringConGen`, and
`RingCon.Quotient`/`lift`. Mathlib's sources are Apache-2.0; their authors
and attribution remain in the imported modules. The construction imposes
the semiring generator relations for zero, one, addition, and multiplication.
It works for a possibly noncommutative semiring without cancellation.

The recovered `SemiringGroupificationDifferences.lean` compiles unchanged
against this reconstructed interface. Its difference normal form,
surjectivity result, and induced ring equivalence passed a targeted full
type/axiom audit along with the reconstructed provider. This is algebraic
support for 7.13; it does not establish the missing geometric isomorphism.

`CentralAwayLocalization` and `GradedUnitNormalization` were recovered,
compiled, and audited separately. Their existing receipts remain valid;
they have not been subjected to another full-section audit.

## Definable geometry

Use the predecessor's actual `Space`, `DefSet`, `Map`, `RVFiniteObject`,
`rvFiniteEssential`, RV operations, RV dimension, and partial RV/Gamma
Jacobians. Do not introduce a replacement language, a second absorbing RV
element, or theorem-shaped saturation assumptions.

`VolumeForms.lean` reconstructs nonzero definable RV-valued densities and
their pullback, parameter extension, and restriction. `RVVolumeObjects`
uses these on the existing finite-volume objects and retains ordinary
RV[0] in degree zero. `RVVolumeMorphisms` states the actual generic RV
and pointwise Gamma compatibility equations on essential parts, matching
the checked Section 2 concrete-volume interfaces and the recovered source
uses. `UniformVolumeData` forgets its auxiliary density only at degree zero.

The recovered `RVCoordinateSelection` needs no Section 7 geometry provider.
The recovered `VFRVFibres` only uses the form interface, so its promoted
copy replaces the unavailable `UnaryVFVolumeFibres` import with
`VolumeForms`. Its proof text is otherwise preserved. The quarantined
recovered copy remains unchanged.

Definitions or still-uncompiled reconstructed sources are not proofs of
7.1–7.15. Source compilation, full types, axiom checks, and affected import
checks are recorded per completed batch. No new Section 5.8 hypothesis is
introduced by this reconstruction.

## Elementary-blowup comparison reconstruction

At the same pinned predecessor revision, `exists_definable_generic_RVJacobian`
supplies actual head and full Jacobians. `isRVJacobianAt_zero_arity` handles
the empty head without changing RV[0]. Section 6's
`Admissible.finite_label_fibres` and the source finite-volume fibres prove
that the unchanged head is finite-to-one. No finiteness conclusion is taken
as an extra saturation premise.

The new tangent calculation uses Mathlib's polynomial renaming, partial
derivatives, polynomial roots, `Polynomial.derivative'`, and determinant
expansion. The punctured vertical line consists of actual corrected chart
points. Its polynomial identity forces the last tangent column; coordinate
projection supplies the head block. Algebraic closedness of the residue
field is obtained from the released `VFAlgClosed.isAlgClosed_vfType` and
`ValOneEC.Johnson.isAlgClosed_residueField` declarations. Imported Mathlib
sources retain their Apache-2.0 attribution.

`elementaryBlowupIso` now compiles with full type and allowed-axiom inspection.
The affected 62-module Library build passed. The complete fourth targeted
batch has 26 exports; its receipt is
`.scratch/recovery/recovered-fourth-geometry-receipt.json`. The theorem uses
only the actual model/BaseContext hypotheses, source isomorphism and two
concrete admissible elementary blowups; no graph-field or new Section 5.8
input was added. Common refinement remains separate work.

## Actual common refinement

The reconstructed volume overlap uses actual source images, complementary
restrictions and density-preserving coproduct maps. The source geometry in
`IntegrationSection6.OverlapRefinement` and `Confluence` was consulted for
its architecture; an ordinary RV diamond was not used as a volume diamond.
`volumeBlowup_diamond` proves the volume statement from the four pieces and
the checked elementary-blowup comparison. The only imported combinatorial
result is `IntegrationInACVF.Section6.Iteration.grid`, whose geometric
hypothesis is supplied by the newly proved volume class diamond.

The exact-length iterated common refinement and transitivity of actual
common-blowup equivalence compiled, passed full type/allowed-axiom review,
and passed the affected 88-module Library build. The 19-source sixth batch
has 70 exports; no new Section 5.8 premise or theorem-shaped model input is
present. The recovered `VolumeBlowupEquivalence`, `VolumeDegreeTransport`
and `OrdinaryZeroVolumeRows` compile against these reconstructed providers.
Ordinary degree-zero rows are support for the retained RV[0] convention,
not an attempt to reopen the excluded empty-selected-set case of 7.5.

## Concrete VF volume category and prescribed lifts

`Section2VolumeBridge` identifies the density and volume-morphism definitions
with Section2.ConcreteVolumeForms and ConcreteVolumeMorphisms. The positive
lift existence theorem reuses the pinned predecessor's actual
`theorem_9_16_finite_volume_of_reference_input`, supplying its graph input
from the checked sequel `ConstructedGaussGraph.acvf_graph_input`. Generation
of the original VF/Gamma base is retained. The reverse descent uses the
checked `corollary_2_34_nonzero`, with actual label compatibility.

The VF category uses native fixed-label partial derivatives, the checked
generic mixed chain rule, actual same-base dimensions, and genuine
subdomain images/preimages. The local determinant-one argument for maps
preserving VF coordinates follows the checked private argument in
Section9.SpecialJacobianGeneric; attribution is recorded in the source.
It does not assert that a Jacobian is defined at every boundary point.
The thirteen-module batch passed 56 full type/axiom inspections and its
affected Library build (9,849 jobs counting cached dependencies).

## Selected density graphs and positive ordered contractions

The paper's v2 HTML/PDF became accessible through the web connector and
Section7 was read directly. Definition7.1 and Lemma7.2 match the concrete
elementary chart and corrected isomorphism. The numbered wrapper is now
checked. Lemma7.5 retains the author-approved nonempty selected E scope.

Density graphs and their actual volume bijections are rebuilt directly.
NativeVolumeDomains converts the same raw points to the pinned Section5
presentations using canonical normalization, without adding parameters.
The construction of ordered augmented objects reuses
`ordered_selected_fibres_finite` and the actual certified preparation
program theorem. All contracted VF labels and selected original labels
remain in their explicit recursive numerical order. Density transport
follows original-label preservation. No comparison theorem is an object
field. The standing VFFieldBase premise remains explicit for existence.
The target fibrewise common-blowup comparison remains open.

The ten-module batch passed65 full type/axiom checks, including named
instances, and its affected Library build passed10,161 jobs with caches.

## Positive products and signed coordinates

Mathlib's actual `Matrix.det_permute`, `det_submatrix_equiv_self` and
`det_fromBlocks_zero₂₁` are used with explicit coordinate maps. Polynomial
tangent projection gives both complementary blocks; generic existence is
kept separate from determinant comparison. The finite-volume maps bound
RV dimensions by volume degrees, so auxiliary label arities do not enlarge
the almost-everywhere threshold. The resulting positive product map has
both genuine volume equations. Degree-zero factors and multiplicative
common-blowup compatibility remain separate work.

The original VolumeCoordinatePermutation and GammaRVVolumeSchemata texts
were promoted unchanged after rebuilding their missing providers. The
function-row validity theorem reuses checked original-base Gamma logical
operations. No arbitrary Gamma representative is silently added to the
generation hypothesis. All56 new exported types/axioms were inspected,
and the affected Library build passed10,173 jobs including cached imports.

## Tenth reconstruction batch: volume graph realization

Reused the checked Section 6 GammaFiniteGraphPresentation, finite-extra code
extension and full Gamma relation specialization. Added a genuine functional
density map using unique row outputs and exact support. Canonical raw RV
adapters use normalize_eq_of_isCanonical on definability proofs while keeping
points and functions unchanged. Presentation independence uses the checked
coordinate/density-preserving volume isomorphism, hence the existing generic
Jacobian proof rather than a new comparison premise. No new references or
dependency changes were introduced.

## Eleventh reconstruction batch: positive products and blowups

Reused native RV cartesian associators, coproduct maps and elementary
right-product coordinate algebra. The new explicit distributivity chart
retains pointwise coordinates and densities. The recovered signed product
swap was promoted with narrowed imports; its original text remains in
quarantine. Named determinant signs belong to the native residue parameter
field. Left multiplication of elementary blowups is proved by an actual
product chart and algebraicity monotonicity. Right multiplication of common
blowups follows from the signed swap and a proved common rescaling operation.
Only the new batch and affected library were audited; no full repeat was run.

## Twelfth reconstruction batch: ordinary RV[0] products

Reused native finite RV products and coproduct charts, the checked generic RV
Jacobian theorem and nested-correspondence comparison. The actual essential
product is conjugated to the positive essential domain times the ordinary
RV[0] domain. Only the positive Jacobian is used; the other domain's dimension
bound is zero. Original unit-isomorphism source was promoted unchanged.
The zero-factor elementary chart retains the old last coordinate and density,
and yields actual multiplicative common-blowup compatibility without point
cancellation. No new citations or dependencies were introduced.

## Thirteenth reconstruction batch: all-degree multiplication

Connected the actual original product with the zero-factor charts using
coordinate/density-preserving isomorphisms. All-degree MuIsp multiplicative
congruence is proved by its four degree cases. Both all-degree quotient
families use the actual coproduct and the proved product, with an additive
projection that preserves multiplication. Native cartesian reassociation
and singleton-unit maps provide full product associativity and unit maps;
the density proof uses ordinary multiplication, including the zero-degree
convention. No commutativity of the full volume ring is used.

## Fourteenth reconstruction batch: graded semiring congruence

Used the actual coproduct fold charts on both sides, retaining coordinate
order and density. All-degree density data handles the ordinary RV[0]
convention without adding a point. The pinned Mathlib DirectSum.GMonoid and
GSemiring interfaces assemble the proved geometric coherence laws. Both
quotients are actual direct-sum semirings and the canonical projection is
surjective. Fresh comparison with arXiv:0809.0473v2, Section7 lines1113–1120,
identifies the completed relation statement as Lemma7.4. No external theorem
or new generation hypothesis is used.

## Fifteenth reconstruction batch: uniform volume certificates

Reused pinned predecessor Section4.RVParameterInvariance.rvDim_extend_le,
Section4.SmallGeneratedBase.small_generated_finite_extension, and the actual
Section6.ParameterExtension maps. The parameterized chart normalization,
certificates and output adapt the logical construction in the predecessor's
Section9.VolumeChartCertificates, VolumeChartOutput and
ResidueChartCertificateLogic; the native arithmetic and tangent proofs are
imported directly. The finite generic cover uses
exists_finite_volume_chart_cover and
exists_chartValue_of_full_volumePair_dimension from the pinned Section9
sources. These are already formalized results, with the original canonical
structure, BaseContext, finite-volume, nonzero-coordinate and positive-degree
hypotheses retained. Revision remains 9cc9760892092dd34cfad4a6dee655843c52f30c;
no dependency or citation was added. No LICENSE file was available at that
checkout root, so no new licensing claim is made for adapted source.

The 14-module/45-export batch passed compilation, its complete 609-line
type/axiom review, and the affected 10,235-job library build. These formulas
encode actual chart values; they do not assume a definable common-blowup
relation or supply the unfinished witness cover for7.5.

## Sixteenth reconstruction batch: original-base chart coding

The generic finite RV-map bound reuses the already checked Section6
gamma_uniform_finite_tuple_rows theorem, with the empty imaginary base and
explicit normalization transport in a canonical model. Gamma chart descent
uses the original invariant Relation interface and equality of representative
rows, rather than extending the conclusion's base by chosen representatives.
The tuple coordinate operation has separately proved uniform definability
and proper-sort preservation. Exact schema restrictions reuse native
gamma_family_row_exists_definable and finite-map row validity; reverse-fibre
bounds decrease on restriction. No pin or reference changed. The8-module/
30-export batch passed complete425-line type/axiom review and the affected
10,243-job Library build; these checks do not certify full7.5.

## Seventeenth reconstruction batch: finite formula criterion

Reused native TupleBlockSwap inversion, original-Gamma row projection and
preimage operations to derive actual volume correspondences. A direct
parameter-free recursive product term uses only released RV multiplication
and1. The native raw valuation preorder supplies Gamma product balance;
the proof retains the distinction between equality in Gamma and in RV.
The already checked essential Gamma weight, generic chart certificates and
small-dimensional exceptional maps give both directions of the fixed-chart
volume-isomorphism criterion. No external theorem, pin change, generation
claim or new geometric premise was introduced. The8-module/29-export batch
passed full418-line type/axiom review and the10,251-job affected Library build.

## Eighteenth reconstruction batch: full volume validity formulas

The native RVFinitaryFunction.dimension_image_le theorem applies to the
singleton values of an actual definable map. Together with native finite
RV append maps it moves exceptional sets to coordinate-and-density labels
without increasing dimension. Their finite maps and uniform bounds are
derived from the checked source certificate. Native real/Gamma row
projection/subset operations express Gamma product balance and the
supported Jacobian graph with the actual density ratio. The native
GammaFiniteRVIsoSchema is reused on the exact essential source/target
schemata. No graph-field premise, outside citation, generation assumption
for internal codes or dependency change was introduced. The10-module/
49-export batch passed639-line full review and the10,261-job Library build.
Schema realization/promotion is explicitly outside this checked boundary.


## Nineteenth reconstruction batch: semantic realization

Reused native `Map.ofFunctionalRelation` and its graph specification, native
bijective row validity/unique reverse fibres, and the checked finite-map
characterization of RV dimension. Native Gamma real specialization supplies
only finite internal representative codes. The existing canonical raw-map
and parameter-extension interfaces retain literal coordinates and density.
The new exact row semantics prove both volume clauses and identify the
schema-derived coordinate correspondence with the actual map's image.
The original Gamma chart is retained exactly in the conclusion. No pin,
citation, graph-field premise or generation assumption was added. The
10-module/30-export batch passed712-line full review and the10,271-job build.
Promotion and complete common-blowup witness compactness remain open.


## Twentieth reconstruction batch: object promotion and exception names

Native gamma_sorted_finite_object_promotion and tuple-relation promotion
are reused on the actual coordinate graph and on the density viewed as an
ordinary Gamma RV-valued function. Its fibres are not required finite.
The full density graph and a nonzero guard prove exact promoted rows.
Native first-order row projection existentially hides auxiliary exception
names. Source/target coordinate and density graphs and the comparison
chart never depend on those names. Exact semantic interpretation and
finite-map dimension bounds prove soundness in a containing BaseContext.
No new citation, pin, definable-choice principle or generation assumption
was added. The10-module/24-export batch passed535-line full review and the
10,282-job affected build. Promotion of complete comparison witnesses and
the later common-blowup compactness/gluing are still open.


## Twenty-first reconstruction batch: comparison promotion

Native Substructure.closure_induction and DefinableConstants.function_symbol/
eliminate_parameters prove raw parameter elimination for term closure.
The actual finite map then gives a GammaFiniteGraphPresentation over the
named generators; checked native finite-object promotion supplies its
exception schema with the same dimension and exact domain. Native raw
Gamma graph flattening and tuple-relation promotion retain the original
comparison chart. Actual essential bijectivity, constant nonzero-coordinate
weight and the checked finite chart certificate prove all validity clauses.
The combined promotion theorem explicitly assumes a named term-generated
internal context and the full original-Gamma comparison graph; it does not
infer either from arbitrary real containment. No new reference, pin or
geometric premise was introduced into the7.5 target. The12-module/23-export
batch passed625-line full review and the10,294-job affected build. Common-
blowup formula operations, witness promotion/cover/gluing and7.5 remain open.


## Twenty-second reconstruction batch: geometric density formulas

Native same-row formulas, graph presentation congruence, label-image/tagged
coproduct formula operations and elementary coordinate programs are reused
without changing the pins. The density template uses their formula fields
only and does not claim finite fibres. Nonzero density guards preserve the
given typed rows. Native tag injectivity/disjointness proves coproduct
functionality; the old-label projection proves elementary functionality.
Actual native coproducts and explicitly Gamma-admissible elementary objects
provide valid finite bounds. Full coordinate/density row equality and the
proved comparison validity yield the first-order blowup-witness locus.
No new citation, geometric input or internal field-generation claim was
introduced. The10-module/33-export batch passed441-line full review and the
10,304-job affected build. Geometric blowup witness realization/promotion,
common chains, finite-cover/indexed-gluing and7.5 remain open.


## Twenty-third reconstruction batch: actual formula semantics

The twenty-third batch connects the coproduct and elementary formula rows
to actual volume objects, preserving their full coordinate and density
graphs. Original-Gamma admissibility transfers to every containing small
context by the checked algebraicity theorem. Comparison certificates now
act on arbitrary actual endpoint interpretations and keep their exact
original charts through finite internal parameter extensions.

`GammaRVVolumeBlowupSchema.realizeOn` realizes every valid witness as an
actual `VolumeBlowup` of the interpreted endpoints after a finite internal
base extension. The center, remainder, elementary chart and both volume
isomorphisms are constructed. No field or VF/Gamma generation property is
asserted for the extension. This proves soundness; promotion of every
required original-Gamma geometric witness, common chains, finite-cover/
indexed gluing and positive selected7.5 remain open.

The12-module/19-export batch passed full342-line type/axiom inspection and
the affected10,316-job Library build. Earlier source leaves were unchanged
and were not manually audited again. The252-module CI run43591052527 is
separate and remains in progress at this checkpoint.


## Common volume witnesses and their finite cover

The twenty-fourth batch proves actual promotion of volume objects,
isomorphisms, admissibility, blowups, finite chains and common forward
blowups over the term context of the original named parameters. Parameter
elimination supplies full original-Gamma graph definability and descends
admissibility; it adds no field or VF/Gamma generation hypothesis.

Finite chain and common-witness schemata have proved first-order validity.
Their sound realization retains exact chain lengths. The compactness
result `gamma_volume_common_finite_witness_cover` starts from actual
common forward blowups in those named contexts and gives a finite family
of valid witnesses, with a common bound on both chain lengths. It does not
assume that an abstract common-blowup relation is definable.

The10-module/26-export batch passed the complete540-line type/axiom review
and the10,328-job affected Library build. Indexed volume gluing and the
selected-family contraction comparison of positive selected7.5 remain
open. The remote backup is still the264-module commit6638f17. At the user's
request, further GitHub backups will be spaced about100 new modules apart;
the next planned backup is around364 modules. Targeted local verification
continues as proofs are added.



## Indexed volume objects and fibre Jacobians

The twenty-fifth batch constructs actual joint indexed volume
presentations, appending the index volume to the fibre coordinates and
retaining the fibre density. Their actual parameter fibres interpret the
original schema rows exactly. Essential joint labels have precisely a
nonzero base-volume tuple and an essential fibre label. Uniform valid
comparison charts yield the actual underlying essential bijection with
its exact original-Gamma joint chart; its volume equations remain separate.

Polynomial maps carry tangent vectors to their differential images. A
fixed-head fibre tangent embeds vertically, and the full correspondence
matrix has the fibre determinant. Thus any defined full RV Jacobian equals
the defined fixed-head fibre Jacobian. The generic-existence theorem is
kept separate. Coordinate bases and algebraic-parameter elimination prove
the RV dimension bound by base dimension plus a fibre bound, without
choosing definable fibre maps. Small-parameter invariance descends a
definable exceptional set from a containing context, whose smallness at
the original cardinal is now retained by certificate realization.

The14-module/37-export batch passed the full652-line type/axiom review and
the10,354-job affected Library build. Full indexed Gamma/RV volume
preservation, indexed blowup/common-witness gluing and the positive
selected7.5 contraction comparison remain open. GitHub backups remain
spaced about100 new modules apart, with264 saved remotely and the next
planned near364.



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


## Arbitrary rectangle contractions

`rectangle_opposite_order_contraction_comparison` proves the rectangle case of Lemma7.7 for arbitrary specified id/swap original-Gamma contractions of the same actual fixed-label native product of two pure unary domains. It produces common forward Gamma volume-blowup chains on their actual normalized finite volume objects, retaining the selected nonzero density. The factors need not be open balls. `gamma_named_rectangle_contraction_comparison` works in the common-name context of the original base and proves preservation of original VF independence internally; no VFFieldBase hypothesis is added. The remaining hypotheses name a nontrivial Gamma scale and the original real/Gamma context and label tuple.

`TwoOrderRectanglePreparations` is constructed from actual unary special chains in one prescribed common-name context. Both orders retain all original fixed labels, and their second stages carry the entire first RV contraction. Their raw objects map to one actual finite unary product with each VF volume coordinate preserved. Unary finiteness and deletion of the carried constant labels are proved from the actual chains. Full original-Gamma graph certificates compose on these actual maps.

`fullContractionNormalizationVolumeIso` proves full-dimensional raw-to-normalized volume compatibility in every positive degree. The rectangle comparison uses the full coordinate-preserving Jacobian criterion, since rectangle RV objects may have dimension two. `fixed_label_contraction_constant_density` identifies the actual retained-coordinate density object with its constant-density normalized object for any specified contraction. Corollary7.6 applied to the identity compares arbitrary specified same-order contractions to the constructed programs; contexts are then joined to obtain the two opposite-order common chains. This follows the paper’s unary product argument while making its actual finite objects and density maps explicit.

The23-module/103-export batch passed actual source compilation, one full2,222-line type/axiom review and affected Library integration. The checked boundary is788 modules plus Library and2,411 exports. Earlier batches were not manually audited again. The balanced and degenerate cases remain proved. The nonbalanced-cell rectangle-presentation adapters, uniform4.8 family assembly and higher-dimensional exchange still need completion;7.7-7.15 remain open.


## Every definable two-cell

`gamma_definable_named_cell_contraction_comparison` proves the pointwise two-cell case of Lemma7.7 for every actual original-Gamma `Cells.DefinableTwoCell` and arbitrary specified id/swap contractions of its fixed-label source. The resulting common forward Gamma volume-blowup chains compare their actual retained-density normalized objects in a genuine containing context. The positioning function and paradigms come from the cell data. Their real presentation names, including both balanced paradigms, are supplied internally; no separately named RV paradigms or translation centres are assumed.

The context `gammaDefinableNamesVolumeContext` is the actual definable closure of the original real/Gamma names. `small_definable_closure` proves its cardinal bound by an injection into singleton-defining LRV formulas. Its VF coefficient field lies in an algebraic extension of the original field, so original VF independence is preserved. A Gamma-definable singleton belongs to this context. This closes the presentation gap in the balanced case.

`nonbalanced_cell_contraction_comparison` uses the checked Section4 rectangle theorem and the actual two unary projection images; their domains retain the original Gamma base. Thus it includes the permitted singleton first-projection boundary. The zero-paradigm case uses the previously checked small-VF-dimension comparison. Balanced nonzero paradigms follow from the checked simultaneous-degeneracy equivalence.

The8-module/14-export batch passed actual source compilation, one full339-line type/axiom review and affected Library integration. The checked local boundary is796 modules plus Library and2,425 exports. Earlier batches were not manually audited again. Full7.7 still needs the uniform cell-family/refinement assembly and higher-dimensional coordinate exchange. For4.8, retain the paper’s standing VF/Gamma generation scope already recorded in TARGETS.md; do not assert the existing cell-decomposition theorem without that hypothesis. The paper’s stated setting and proof of7.7 were rechecked at arXiv:0809.0473v2, abstract, Convention2.1 and Lemma7.7. No new Section7 assumption has been introduced.


## Mixed-label cell refinement and volume preservation

`mixed_two_cell_decomposition` extends the checked Section4 vertical-chart, positioning-row and paradigm constructions to arbitrary old RV labels. It supplies an actual original-Gamma RV map whose equal-output fibres retain the old labels and are definable two-cells over their output label base. No pointwise existence axiom or new5.8 input is assumed. The standing `VFGammaGeneratedBase` hypothesis of4.8 is explicit.

`two_cell_volume_refinement_exists` proves the actual refinement step of7.7 for any positive VF² object with a retained-coordinate density. Its graph map preserves all VF coordinates, literally retains all old RV labels, is relatively unary with respect to either coordinate, has finite RV fibres, and carries its complete original-Gamma graph certificate. `nativeRVGraphVolumeBijection` is an actual VF-volume bijection for an arbitrary transported density. The selected density remains the same old label at `Fin.castAdd d j`.

`rv_parameterized_cell_contraction_comparison` extends the completed pointwise cell comparison to an arbitrary finite RV parameter tuple. `gammaRVDefinableNamesVolumeContext` is the actual small definable closure of the original names together with that tuple. It names the cell paradigms and preserves VF independence over the original coefficient field; no generated-base assertion is made for the RV-augmented parameter base.

The13-module/52-export batch passed actual compilation, one complete919-line type/axiom review, and affected Library integration. The checked boundary is809 source modules plus Library, with2,477 exports. The old batches were not manually audited again. The global volume comparison of the whole two-cell family is still open: a fibrewise RV-dimension bound is not asserted for the global family. Full7.7 still needs that comparison and higher-dimensional exchange;7.8-7.15 remain incomplete.


## Specified contraction reduction and uniform vertical geometry

`two_order_cell_family_reduction` reduces two actual specified VF² standard contractions, in any two orders, to actual Gamma-certified contractions of one common definable two-cell family. The two forward volume-blowup comparisons are realized in one genuine containing context. `rv_graph_refinement_contraction_common_blowup` proves the reduction for arbitrary finite-label sources in every positive VF degree, with their literal nonconstant retained density. `gamma_named_two_cell_contraction_reduction` constructs the common-name context and discharges VF-independence preservation internally. `generatedBaseVFField` derives the actual field convention from the already standing generation hypothesis, supplying the checked all-order program producer without a separate field-base assumption.

`UniformMixedCellPresentation` retains the actual global vertical chart, scalar RV refinement and positioning rows behind4.8. The refined centre has an actual native map and complete original-Gamma graph. `refinement_centre_constant` proves its independence from the active VF coordinate when all other VF and refined RV labels are fixed. `source_head_fibre` identifies every complete source head fibre with its actual translated RV class. The corresponding whole-family `verticalTranslation` is bijective onto an original-Gamma head-saturated image, and `vertical_translation_jacobian_one` proves its global AE VF Jacobian equals1. `vertical_translation_standard_contraction_exists` constructs an actual contraction of that image by identity on the complete head fibres followed by unary special preparation over the same common names.

`mixed_translation_contraction_common_blowup` extends the translation comparison to arbitrary carried RV labels in every positive VF degree. Target finiteness follows from the checked Gamma-bijection finiteness theorem; the same literal density coordinate is retained. `rv_cell_family_fibre_contraction_comparison` applies the completed pointwise cell theorem to each actual nonempty labelled fibre, constructing its native pure-VF presentation and all name/tuple certificates.

The17-module/52-export batch passed actual compilation, one complete1,058-line type/axiom review, and affected Library integration. The checked boundary is826 source modules plus Library, with2,529 exports. Earlier batches were not manually audited again. The global opposite-order comparison on a whole cell family remains open: uniform horizontal/product geometry and its full global RV-Jacobian calculation are still needed. Do not promote the pointwise dimension-one calculation to a global RV-dimension bound. Higher-dimensional exchange and7.8-7.15 remain incomplete.


## Uniform balanced horizontal geometry and contraction reductions

The actual mixed positioning map of a balanced-row family is now an original-Gamma bijection retaining every RV label. Its image is exactly the labelled head projection. Inverting that map constructs the actual horizontal centre, whose full graph remains over the original Gamma base and whose value is constant when the other VF coordinate and all RV labels are frozen. Every complete horizontal source fibre is its translated RV class. The whole-family horizontal translation is bijective with VF Jacobian one almost everywhere; after swapping VF coordinates its image is head-saturated and has a constructed opposite-order standard contraction.

`position_compatible_preparation_exists` constructs both compatible unary special preparations and the bijection of prepared RV keys in a genuine small containing context. No finite-unary-label hypothesis is inserted. `vertical_contraction_reduction` and `horizontal_contraction_reduction` connect specified contractions of the actual graph family to constructed contractions of the corresponding translated families by common forward original-Gamma volume blowups. Their density is the same literal original RV coordinate, including nonconstant densities.

The15-module/53-export batch passed actual compilation, one complete1,019-line type/axiom review and affected Library integration. The checked boundary is841 source modules plus Library, with2,582 exports. Earlier batches were not manually audited again. These results complete uniform horizontal geometry in the explicit `BalancedRows` subcase. They do not yet prove the global RV-volume comparison between the two translated families. The full global RV Jacobian, the family case partition, higher-dimensional exchange and7.8-7.15 remain open. The fixed-parameter dimension-one argument is not used as a global dimension bound.


## Actual case partition and selected family geometry

`shape_partition` and `native_shape_partition_cover` construct the actual original-Gamma partition of the cell graph family into zero-paradigm, rectangular, and balanced parts. The rectangle test is the existence of two points in one RV-labelled fibre whose mixed coordinates leave that fibre; four VF witnesses give a direct definable predicate. The paradigm is constant on each retained RV label, and its zero set is obtained from the zero-coordinate locus of the actual uniform translation. These case predicates retain the original Gamma base.

`UniformMixedCellPresentation.select` restricts the actual vertical chart and position rows to whole refinement-parameter fibres. The global centre, paradigm and complete parameter fibres are preserved. `balanced_parameter_selection_rows` proves BalancedRows for the selected balanced part. `balancedNativeRefinement` has exactly the original balanced-part carrier, with all old coordinates and finite-label certificates retained. Both actual translated balanced families have constructed standard contractions in the required opposite orders; no new balanced-case premise is assumed in this selected construction.

`zero_native_part_dimension` bounds the whole zero-paradigm family by VF dimension one, even with varying RV parameters. `zero_native_part_contractions_compare` proves the volume comparison for arbitrary specified orders and arbitrary nonzero retained density. The mixed retained-density lift and dimension lemmas generalize the earlier fixed-label support argument.

For a shared-label rectangle family, a unary special preparation of the actual labelled head projection is extended over a free passive VF coordinate and restricted to the family. Exact old-RV-label preservation and rectangularity make inverse membership constant on head RV fibres, giving a genuine head-saturated target. The full graph remains over the original Gamma base. `rectangle_family_standard_contraction_exists` and its swapped version construct both coordinate orders.

The24-module/124-export batch passed actual compilation, one complete1,872-line type/axiom review and affected Library integration. The checked boundary is865 source modules plus Library, with2,706 exports. Earlier batches were not manually audited again. The global nonzero rectangle and balanced RV-volume comparisons and their assembly remain open, including the full global RV-Jacobian argument for balanced families. Higher-dimensional exchange and7.8-7.15 are incomplete. Do not use the fixed-parameter dimension-one calculation as a global dimension bound.


## Whole rectangle families with shared RV labels

`rectangle_family_contractions_compare` proves the entire rectangle-family case of Lemma7.7 for any two specified coordinate orders in VF dimension two. It compares the actual normalized finite contraction objects over the original Gamma base in a genuine containing context. The density may vary across the family: every original RV label is retained literally. The context and VF-independence hypotheses are the same original/common-name hypotheses used by the established contraction reductions.

The proof chooses the two original labelled unary preparations independently. `RVLabelConstraintSpecialPreparation` lifts a special chain through a domain constrained by carried RV parameters, allowing the old and carried label selectors to overlap. Its exact target consists of the prepared unary factor and the carried parameter constraint together with equality of their two copies of the original labels. The head-product map is injective, and its image is exactly the pairs satisfying that equality. This constructs a definable bijection of the two actual rectangle contraction targets by exchanging the two factor keys. Its complete graph stays over the original Gamma base.

`raw_order_map_volume` proves equality of both VF volume coordinates separately. `raw_order_retained_labels` proves equality of every old density label. The actual raw and normalized Gamma RV equivalences therefore realize a full volume isomorphism; no dimension-one bound or constant-density specialization is used. Corollary7.6 applied to the identity compares arbitrary specified same-order contractions to the constructed ones, and the genuine contexts are joined to obtain common forward volume-blowup chains.

A separate actual two-stage rectangle preparation preserves saturation in the first coordinate while preparing the second. Restoring the VF coordinate order gives a bijection to a full RV pullback with Jacobian one almost everywhere in both directions. The general bridge `relative_head_special_vf_jacobian_one` proves the full mixed VF statement from actual special chains on coordinate fibres: full VF independence makes the active head independent over the coefficient field generated by the frozen tail, so the checked unary special-chain derivative theorem applies over its precise parameter base.

The35-module/122-export batch passed actual source compilation, one complete2,208-line new type/axiom review and affected Library integration (11,600 jobs, including cached dependencies). The checked boundary is900 source modules plus Library, with2,828 exports. Earlier batches were not manually audited again. The whole zero-paradigm and rectangle-family cases are complete. The global balanced-family comparison and its full RV-Jacobian calculation, partition assembly, higher-dimensional exchange and7.8-7.15 remain open.


## Balanced valuation products and actual partition restrictions

The actual selected balanced chart now has compatible special preparations over a genuine containing context. The induced RV bijection has a complete graph over the original Gamma base and retains every original RV label literally. The valuation product identity holds on its actual source RV domain, with row slopes and nonzero paradigms derived from the balanced geometry and the actual selected partition. This is a valuation statement; the full RV-Jacobian identity and the balanced-family volume comparison remain open.

Specified standard contractions restrict to each of the three actual native partition pieces over the same small real base and original Gamma base. The restricted targets are literal RV-label cuts of the original target, with unchanged target arity, volume-coordinate selectors and all recursive retained-label selectors. The actual rectangular native piece now inherits the proved whole rectangle-family comparison.

The18-module/61-export batch passed actual source compilation, one complete1,266-line type/axiom review and Library integration (11,622 jobs, including cached dependencies). The checked boundary is918 source modules plus Library, with2,889 exports. Earlier proofs were not manually audited again. Balanced RV-Jacobian comparison, partition assembly, higher-dimensional exchange and7.8-7.15 remain open.


## Matching prepared balls and different-ball rectangle families

The actual compatible preparations now define a matching/different split of the whole balanced graph, over the unchanged original Gamma base. Both prepared coordinate keys are recorded by an actual finite-arity Gamma RV map. Its fibres are exactly the original balanced rows intersected with the two inverse-special balls, with their original RV labels fixed. Different prepared keys give disjoint inverse balls; RV differences between those balls are constant, including the singleton cases. Consequently the actual different-key native family, refined by the two keys, is a rectangle family. `different_prepared_family_contractions_compare` proves its full volume comparison for arbitrary specified VF-two orders and arbitrary retained nonzero density in a genuine containing context.

For matching keys, `matching_prepared_row_balanced_fibres` proves that the restricted row keeps both COMPLETE balanced fibre identities with the original paradigms. Its two inverse-special cells are actual open balls when the vertical paradigm is nonzero. `matching_vertical_prepared_difference` proves exact equality of centred VF differences using the special-chain subtraction formula. These results require no unproved atomicity or RV-linearity assertion. The original whole vertical and horizontal translated families are also proved rectangular over their retained labels.

`pullbackVolumeIsoOfLabelDeterminedMap` constructs an actual RV isomorphism from a specified bijection between full RV pullbacks when shared retained-label selectors determine all RV fibres on both sides, all VF volume coordinates are nonzero, and both volume maps have finite fibres. Full lift-volume descent then proves its RV volume identity from the SAME actual volume-preserving VF map. This is a checked general bridge, not yet a completed application to the matching balanced family. Constructing its actual prepared pullbacks and proving the required label determination remain open. The proposed continuation is recorded as provisional in `.scratch/recovery/matching-ball-volume-route.md`.

The9-module/63-export batch passed actual source compilation, one complete1,302-line new type/axiom review and Library integration (11,632 jobs, including cached dependencies). The checked boundary is927 source modules plus Library, with2,952 exports. Earlier batches were not manually audited again. The global balanced-family volume comparison, partition assembly, higher-dimensional exchange and7.8-7.15 remain open.


## Actual matching-family pullbacks and full volume descent

`matching_prepared_volume_comparison` constructs both recorded-key unary preparations of the actual matching family, lifts them to full VF-two RV pullbacks, and proves an actual original-Gamma RV volume isomorphism between the two prepared key objects. Any nonzero retained family density coordinate is allowed, including nonconstant densities. The compatible positioning preparations are re-presented in the original small common-name context; no new VF-independence hypothesis is introduced.

The actual labelled unary projections contain whole inverse-special fibres. This source-completeness proof establishes the recorded lifts' target pullback property. The full two-coordinate preparations preserve all shared labels; those labels determine every target RV fibre. Their prepared VF coordinates are nonzero because their inverse cells are open, and their translated offsets are the two nondegenerate paradigms of the same balanced row. Finite RV fibres follow from the original family's finite fibres through the actual Gamma bijections.

The VF map between the prepared targets is the specified composition of the inverse vertical preparation, inverse vertical translation, horizontal translation and horizontal preparation. Its full VF Jacobian is one almost everywhere. The SAME induced RV map enters the full lift-volume descent, now with its complete original-Gamma certificate. No arbitrary ordinary RV isomorphism, unproved atomicity or global dimension-one bound is used.

This24-module/124-export batch passed actual source compilation, one complete2,731-line new type/axiom review and Library integration (11,656 jobs, including cached dependencies). The checked boundary is951 source modules plus Library, with3,076 exports. Earlier batches were not manually audited again. The matching prepared-object volume comparison is complete; its identification with arbitrary specified normalized contraction objects remains open, as do matching/different and original case-partition assembly, higher-dimensional exchange and7.8-7.15.


## Matching-family specified contraction volume comparison

`matching_family_contractions_compare` proves the full common forward original-Gamma volume-blowup comparison for any two specified VF-two standard contractions of the actual matching family refined by both compatible prepared keys. The density is any literal retained nonzero family coordinate. The matched family's geometric nonzero-paradigm hypothesis is the one already derived on the selected balanced part; no new RV-Jacobian or prepared-comparison premise is assumed.

The two actual full preparations are relatively unary after restoring the VF coordinate order. Their full targets are shared-label rectangles because their pullback saturation and proved RV-fibre determination force a single pair of RV classes on each labelled fibre. The completed rectangle theorem therefore permits the coordinate order needed by Corollary7.6 at each preparation step. This avoids a new bespoke contraction program through the prepared family.

`canonical_contraction_key_square`, `canonical_contraction_coordinates` and `canonical_contraction_retained_labels` strengthen the existing canonical Gamma finite contraction isomorphism to exact key, entire volume-tuple and all old-label identities. `canonical_pullback_contraction_volume_comparison` then connects the actual pullback coordinate-density volume object to its actual normalized contraction volume object. The containing contexts are joined by `CommonContextVolumeEquivalent.trans`, retaining common forward Gamma blowups throughout. Combining these connections with the actual matching prepared-volume isomorphism and both translations proves the opposite order; Corollary7.6 supplies the same-order cases.

The14-module/25-export batch passed actual source compilation, one complete872-line new type/axiom review and Library integration (11,672 jobs, including cached dependencies). The checked boundary is965 source modules plus Library, with3,101 exports. Earlier batches were not manually audited again. Matching and different-ball refined cases are now individually complete. Their partition assembly, the original zero/rectangle/balanced partition assembly, higher-dimensional exchange and7.8-7.15 remain open.


## Complete VF-two standard contraction volume comparison

`two_vf_standard_contractions_compare` proves the full VF-two case of Lemma7.7 for any two specified standard contraction orders of a Gamma-definable native family with finite RV fibres and any retained nonzero density coordinate. The conclusion gives common forward original-Gamma volume blowups in a genuine containing context. The standing VF/Gamma-generated base, cardinal and common-name context hypotheses, including preservation of VF independence, remain explicit. No unproved RV-Jacobian or atomicity input is assumed.

The matching and different families are complementary RV-label cuts of one actual pair-key refinement. Restrictions of specified contraction programs retain their literal target arities and all volume, density and old-label selectors. Normalization commutes with those cuts, so identity maps identify the actual normalized restrictions with volume-object restrictions. Gamma binary volume partition isomorphisms assemble the whole balanced graph family. The original zero/rectangle/balanced RV-label partition is then assembled by a Gamma ternary volume isomorphism, and Corollary7.6 removes the original graph refinement. All comparisons preserve arbitrary specified contraction orders and nonconstant retained density.

The16-module/44-export batch passed actual source compilation, one complete1,175-line new type/axiom review and Library integration (11,688 jobs, including cached dependencies). The checked boundary is981 source modules plus Library, with3,145 exports. Earlier batches were not manually audited again. Higher-dimensional coordinate exchange, the full all-dimensional7.7 and7.8-7.15 remain open.


## Lemma7.7: all-dimensional first-two contraction exchange

`lemma_7_7_native` proves the original-Gamma comparison for arbitrary specified contractions whose first two coordinates are exchanged and whose remaining coordinate orders agree. `lemma_7_7` states the paper's explicit permutation conditions for actual positive VF volume objects and their existing normalized standard contraction objects. The standing VF/Gamma generation, cardinal and common-name context assumptions remain visible. Arbitrary retained nonconstant density is allowed; no Section5.8 input, RV atomicity or unproved Jacobian comparison is assumed.

The higher-dimensional proof reuses Section6's actual frozen-prefix programs. A generated closure of the frozen coefficient base permits application of the completed VF-two theorem. A new small containing context adds only RV representatives before definable closure; an independent tuple argument proves that its VF coefficient extension preserves the required independence. Definable-name elimination descends full volume objects, elementary charts, algebraic blowup centers and both common forward chains to exactly the original frozen real/Gamma base. The literal raw volume and density rows are recovered from the normalized comparison.

The first two actual contracted VF tags give a selected degree of2, so the accepted positive-degree Lemma7.5 appends the remaining contractions. Exact selector identities, including the first-two permutation and every old density coordinate, identify the resulting rows with the specified full standard contractions. The ordinary RV[0] convention is unchanged.

The12-module/30-export batch passed actual source compilation and one complete671-line new type/axiom review. The affected Library build is recorded in its verification receipt. The checked boundary is993 source modules plus Library, with3,175 exports. Earlier batches were not manually audited again. Lemma7.7 is complete in its recorded standing scope; Proposition7.8 and7.9-7.15 remain open.


## Proposition7.8: common blowups have volume-isomorphic lifts

`ElementaryBlowup.nonempty_volume_lift_iso` constructs the canonical focus using Section6.12, proves its actual VF map has Jacobian1 and retains all original RV labels, and hence preserves any nonzero original density. Literal normalized and actual elementary objects are identified through full coordinate- and density-preserving RV maps. No lift-invariance or Jacobian premise is assumed.

`VFVolumeIso.coprod` joins actual volume isomorphisms using disjoint RV tags while fixing the VF degree. The domain and density of the RV coproduct lift agree literally with those of the tagged VF coproduct. The glued map's Jacobian equation holds away from a definable VF-small exception, and the genuine cofull source and target domains are retained.

`VolumeBlowup.nonempty_volume_lift_iso`, `IteratedVolumeBlowup.nonempty_volume_lift_iso` and `VolumeBlowupEquivalent.nonempty_volume_lift_iso` extend elementary invariance through arbitrary loci, finite forward chains and common forward blowups. `positiveVolumeLiftOnBlowupClasses` is therefore defined on the genuine common-blowup quotient. This proves the common-blowup to equal-lift-class direction of Proposition7.8 in every positive degree over the explicit original VF/Gamma-generated base, including arbitrary nonconstant density. The converse kernel direction and7.9-7.15 remain open.

The23-module/76-export batch passed actual source compilation, one complete1,142-line new type/axiom review and the affected Library build (11,779 jobs including cached dependencies). The checked boundary is1,016 source modules plus Library, with3,251 exports. Earlier types and proofs were not audited again.


## Actual volume densities on Section5.6 factors

The VF Jacobian of any actual mixed definable bijection is nonzero almost everywhere. A total definable Jacobian map, with zero RV values replaced by1, gives an actual nonzero density. `transportedVFVolumeForm` transports any original density through a genuine bijection, and `preserves_transported_vf_volume` proves the full almost-everywhere volume equation. Multiplication, inversion and division of actual forms are definable.

`unary_chain_volume_data_of_composite` assigns actual intermediate forms to every finite relatively unary factorization of a volume-preserving composite. Its proof uses transported densities and cancellation, with no assumption that arbitrary Section5.6 factors have Jacobian1. `unary_chain_realize_common_names` realizes the original Gamma factors over a fixed base containing their common names, retaining their point maps and Gamma certificates. `unary_partition_volume_densities` attaches these densities to each actual Section5.6 partition factor and retains pointwise agreement with the specified original map. The kernel converse of Proposition7.8 still requires contraction-order comparisons retaining already selected RV coordinates and final partition assembly; it is not claimed by these support results.

The10-module/28-export batch passed actual source compilation, one complete457-line new type/axiom review and the affected Library build. The checked boundary is1,026 source modules plus Library, with3,279 exports. Earlier types and proofs were not audited again.


## Selected RV coordinates realized by actual VF tails

`selectedRVVFTailLift` realizes a selected RV tuple by additional VF coordinates satisfying their literal RV equalities, including selected zero values. Projection onto the original domain is surjective, and finiteness at fixed selected labels becomes actual finite RV fibres. The construction uses no additional real or Gamma parameters.

Maps retaining the selected labels lift while fixing every added VF coordinate. Their literal projection/tail formulas, bijectivity, original-Gamma graphs and relative unary coordinate are proved. An active unary fibre is precisely the original coordinate fibre cut by the fixed RV tuple of the added VF tail. Restricting the supplied genuine unary special preparation proves relative specialness of the lifted map; no global special-chain lift is assumed.

`HeadPreparation.selectedVFTail` lifts any specified head preparation and proves both relative specialness and head saturation. Taking its contracted image commutes with the selected VF realization, with the selector shifted past the actual new RV head tag. These are support results for comparison of contraction orders retaining already selected RV coordinates. They do not yet assert full selected contraction-program comparison or the Proposition7.8 converse.

The13-module/54-export batch passed actual source compilation, one complete865-line new type/axiom review and the affected Library build (11,831 jobs including cached dependencies). The checked boundary is1,039 source modules plus Library, with3,333 exports. Earlier types and proofs were not audited again.


## Full selected VF-tail programs and their RV projection

`selectedRVVFTailPartialProgram` lifts every specified ordered contraction program while leaving the selected VF tail uncontracted. The induction uses the actual lifted head preparations, literal endpoint equalities and selector identities. Its full program graph remains definable over the original Gamma base. Appending the canonical ordered contraction of the remaining RV pullback produces a full program and a contractible tail map fixing all remaining VF coordinates.

`canonicalSelectedTailRVProjection` maps the final pure RV domain onto the original contraction domain by retaining its literal old RV suffix. Contractibility proves injectivity; the VF-tail projection proves surjectivity. Its graph is definable over the original Gamma base. The complete program's original VF volume block, added selected-volume block and retained density agree pointwise with the corresponding coordinates after this projection. These are construction and coordinate results; the actual RV volume chart and selected contraction-order comparison are still to be assembled.

The15-module/49-export batch passed actual source compilation, one complete685-line new type/axiom review and the affected Library build (11,846 jobs including cached dependencies). The checked boundary is1,054 source modules plus Library, with3,382 exports. Earlier types and proofs were not audited again.


## First-two exchange with retained selected RV volume

`selected_first_two_standard_volume_exchange` proves common forward Gamma volume blowups for arbitrary standard contraction programs whose orders exchange their first two coordinates and agree thereafter. The source need only have finite RV labels at fixed VF coordinates and fixed selected RV tuple. Every selected old RV coordinate and the retained nonconstant density remain part of the actual volume object. The real base is the specified context; its standing Gamma cardinality, common-name and VF/Gamma generation hypotheses are explicit. No Section5.8 input is introduced.

The proof realizes the selected tuple by additional VF coordinates over the same base. The full lifted program is an actual standard contraction in the extended order, with exact restored VF selectors. Its canonical final RV projection is bijective, preserves the entire original-order VF block, the selected old RV block and the density, and induces the genuine volume isomorphism `selectedVFTailVolumeIso`. Raw-to-normalized contraction volume comparison then permits applying completed Lemma7.7 and descending through these charts. Simultaneous coordinate restoration avoids identifying contraction-order tags with original-coordinate tags.

This closes selected first-two exchange. Same-head induction and arbitrary-order independence remain to be assembled before the Proposition7.8 converse;7.9-7.15 are still open. The17-module/37-export batch passed actual source compilation, one full748-line new type/axiom review and the affected Library build (11,865 jobs including cached dependencies). The checked boundary is1,071 source modules plus Library, with3,419 exports. Earlier proof types were not audited again.


## Arbitrary contraction-order independence with volume

`selected_volume_contraction_order_independent` proves arbitrary-order comparison on actual selected-volume objects in every positive VF arity, with every selected RV degree (including zero) and arbitrary retained nonzero density. `retained_density_arbitrary_order_contractions_compare` transfers this to the actual normalized finite contraction objects. `standard_volume_contraction_order_independent` applies it to any actual positive VF volume object with its original form and any supplied pair of standard contraction orders. The standing VF/Gamma generation, Gamma cardinality and common-name hypotheses are explicit; no Section5.8 input is present.

The common-head induction retains one specified head preparation. Conjugating by a permutation of the frozen VF tail gives a genuine relative special preparation: its unary coordinate fibre is literally the original fibre, and the original special bijection extends along the proved inclusion of frozen parameter bases. Its contracted image commutes exactly with the tail permutation. The smaller-arity comparison retains the new head RV tag, all old selected coordinates and density. Actual RV volume isomorphisms transport it through one common permutation restoring the original VF order. Same-order comparison connects these constructions to the supplied programs. Two different first coordinates are joined by the checked finite permutation bridge and the proved selected first-two exchange.

This closes arbitrary-order independence needed for Proposition7.8. The remaining kernel converse requires volume comparisons along the actual Section5.6 unary factors and finite partition assembly, followed by the almost-everywhere restriction argument. Statements7.9-7.15 remain open.

The22-module/45-export batch passed actual source compilation, one complete715-line new type/axiom review and the affected Library build (11,890 jobs including cached dependencies). The checked boundary is1,093 source modules plus Library, with3,464 exports. Earlier types and proofs were not audited again.


## Full volume-bijection kernel on RV-pullbacks

`relative_volume_contractions_all_orders` and `unary_chain_volume_contractions_compare` compare any supplied standard contractions along actual relatively unary maps and finite factor chains, with genuine intermediate volume forms. Actual chain inversion and append preserve this volume data. No Jacobian-one hypothesis is imposed on arbitrary Section5.6 factors.

`native_volume_unary_partition_exists` constructs the actual finite Section5.6 partition over the original real context, retaining its point maps and restricted original volume forms. `native_prepared_mixed_partition_exists` constructs simultaneous global special preparation with genuine restricted special bijections on every piece. `prepared_piece_volume_chain_exists` conjugates the actual factors by these preparations, with the transported nonconstant density retained literally in the old RV suffix. `finite_pullback_volume_partition_gluing` assembles actual common volume blowups of all pieces.

`pullback_volume_bijection_kernel` therefore proves the kernel comparison for full volume-preserving bijections between actual positive-dimensional RV-pullbacks. All finite-label, finite-volume, original-base generation, Gamma cardinality and common-name conditions remain explicit. The remaining Proposition7.8 converse needs the almost-everywhere restriction argument and the original RV-object adapters. Statements7.9-7.15 remain open.

The21-module/41-export batch passed actual source compilation, one complete1,003-line new type/axiom review and the affected Library build (11,915 jobs including cached dependencies). The checked boundary is1,114 source modules plus Library, with3,505 exports. Earlier types and proofs were not audited again. The last remote backup remains1,071 modules; the next is due around1,171.


## Proposition7.8: the actual volume lift kernel

`proposition_7_8` proves, in every positive degree, that the full lifts of actual RV volume objects are almost-everywhere VF-volume-isomorphic if and only if the original RV volume objects admit common forward volume blowups. Arbitrary nonconstant densities and coordinate-zero loci are retained. The actual original real context, VF/Gamma generation, Gamma cardinality, nontrivial Gamma and common-name containment hypotheses are explicit. `positive_volume_lift_on_blowup_classes_injective` is its quotient consequence. No Section5.8 input or graph-field hypothesis was added.

For the converse, the actual Section5.6 partition of the cofull source and target is completed by adjoining the discarded complements. The genuine restricted special preparations conjugate the factor chains. The discarded pieces become pullbacks with empty essential volume objects, by their smaller VF dimension and actual special bijectivity, so finite volume gluing applies to the entire partition. Literal native lift charts and actual RV density graph isomorphisms transfer the result to the original RV volume objects.

The original parameter base is recovered without treating a containing-context witness as an original-base proof. `rv_maps_equal_ae_descend` descends the definable disagreement locus by RV-dimension parameter invariance. `rv_jacobian_ae_descend` compares the prescribed density ratio to the original-base generic Jacobian, using actual Jacobian uniqueness. `RVVolumeIso.descend` therefore recovers the two original volume laws. Every original-Gamma carrier, function, full elementary chart and algebraic center is reinterpreted over the contained common names. `CommonContextVolumeEquivalent.descend` preserves the exact finite chain lengths and returns genuine original-base common blowups.

The23-module/47-export batch passed actual source compilation, one complete991-line new type/axiom review and the affected Library build (11,938 jobs including cached dependencies). The checked boundary is1,137 source modules plus Library, with3,552 exports. Earlier types and proofs were not audited again. Statements7.9-7.15 remain open. The last remote backup remains1,071 modules; the next is due around1,171.


## All-degree integration equivalence and actual VF products

`proposition_7_8_all_degrees` proves the lift kernel in every degree. Degree zero remains the ordinary finite VF/RV categories; no density or essential-locus replacement was imposed there. `volumeIntegrationEquiv` and `proposition_7_9` prove the homogeneous additive integration equivalence in every degree. In positive degree, actual density graphs and genuine special transformations produce a full volume-preserving bijection to an actual RV lift. In degree zero, Section5.7 finite lift presentations are transported back to the original canonical structure, and actual ordinary lift isomorphisms are recovered from and descend to actual RV isomorphisms.

Addition is represented by actual fixed coproducts in every degree. `zero_vf_volume_coprod_class` identifies the degree-zero transported additive structure with the actual ordinary VF coproduct. Positive degrees use the actual volume coproduct isomorphism. The original real context, VF/Gamma generation, Gamma cardinality, nontrivial Gamma and contained common-name assumptions remain explicit. No Section5.8 input is added.

`PositiveVFVolumeObject.prod` uses the genuine concatenated VF/RV Cartesian domain and product of the original densities. `has_vf_jacobian_block_product` and `has_mixed_vf_jacobian_product` prove the actual block determinant calculation; `vf_almost_everywhere_product` controls the union of the genuine product exceptional sets. `VFVolumeBijection.prod` constructs full actual volume-preserving product bijections. Extending these to cofull volume isomorphisms and proving the graded multiplicativity in7.10 are the next targets;7.11-7.15 remain open.

The23-module/65-export batch passed actual source compilation, one complete859-line new type/axiom review and one affected Library build (11,961 jobs including cached dependencies). The checked boundary is1,160 source modules plus Library with3,617 exports. Earlier proofs were not audited again. The last remote backup remains1,071 modules; the next is due around1,171.


## Theorem7.10: graded integration and actual multiplication

`volumeGradedIntegrationEquiv` and `proposition_7_10` give the graded semiring equivalence from actual VF volume classes to actual RV common-blowup classes. `volume_graded_integration_lift` and `theorem_7_10` characterize it on full lifts in every degree. The additive structures retain actual fixed coproducts. The generic `gradedAddEquivGSemiring` preserves the existing componentwise addition while obtaining semiring coherence from the proved RV graded semiring.

The product operation is justified geometrically before using its transport presentation. `VFVolumeIso.prod` constructs actual volume-preserving bijections between cofull product subdomains; their complements are controlled by actual VF dimension. `volumeLiftProductBijection` compares the actual product of full lifts to the full lift of the actual RV product, retaining both original nonconstant densities. `positive_volume_integration_product` proves the resulting Cartesian multiplicativity. In ordinary degree zero, `zeroVFVolumeClassesProduct` uses the genuine ordinary VF Cartesian product and `ordinaryZeroLiftProductIso` compares it with the ordinary product lift.

For mixed degrees, `PositiveVFVolumeObject.prod_zero` is the genuine Cartesian product with an ordinary RV[0] full lift; its density is exactly the original positive density. `VFVolumeIso.prod_zero` respects both actual cofull volume isomorphisms and ordinary coefficient isomorphisms. `positiveVFZeroCoefficientProduct` and `positive_volume_integration_zero_coefficient_product` identify this action on quotient classes. The ordinary zero-degree integration equivalence supplies a full-lift presentation of any ordinary VF[0] class. `vf_volume_classes_product_positive_zero` and `vf_volume_classes_product_zero_positive` identify both orders of the mixed product. Moving this zero factor changes no positive VF coordinate order and introduces no Jacobian sign. Positive-positive swaps are not asserted to be unsigned commutative.

The19-module/66-export batch passed actual source compilation, one complete1,032-line new type/axiom review and the affected Library build (11,980 jobs including cached dependencies). The checked boundary is1,179 source modules plus Library with3,683 exports. Earlier exports were not audited again. Function integration7.11-7.12 and the ring/normalized-coefficient applications7.13-7.15 remain open. The next remote checkpoint is due now,108 modules after the last1,071-module backup.


## Volume-family realizations and exceptional base sets

`positive_volume_integration_standard_contraction` computes the proved integration equivalence by any actual specified standard contraction of the original density graph, in any VF order. `positive_volume_integration_coordinate_density` handles a literal retained density directly. `selected_coordinate_volume_realization_integral` computes the integral of an actual full VF realization of a selected RV family using the selected contraction with the original VF coordinate block first. The source density remains arbitrary and nonconstant.

`selected_family_integral_comparison` descends the actual fibrewise7.5 comparison to the original base. `PointwiseRVVolumeFunction` and its integral are defined using actual parameter-context RV common-blowup classes. The appended coordinate convention of this preliminary integral is explicit. `selected_family_canonical_integral_value_independent` transfers the result to the VF-first canonical convention through a common explicit coordinate permutation on both comparison objects, preserving the actual densities. `selected_family_canonical_integral_realization` identifies that value with integration of a genuine full VF realization. No unsigned single-object permutation is assumed.

`SelectedVFVolumeFamily.fullLift` realizes the selected RV tuple by extra VF coordinates with finite RV fibres. Its dimension is at most the VF dimension of the family domain plus the selected degree. RV labels add no VF dimension to a base locus. `selectedFamilyCofullLiftIso` and `full_volume_lift_class_outside_base` remove actual definable VF-small base exceptions by genuine cofull volume isomorphisms. `selected_standard_volume_integral_zero_of_small_domain` proves that a selected family supported on a VF-small domain integrates to zero. `AERVVolumeFunction` is the actual quotient by equality away from a definable smaller-dimensional base set; descent of its integral and coordinate fibre pushforwards are still open.

`volumeIntegrationRingEquiv` applies universal semiring groupification to the actual7.10 equivalence. This establishes the ring equivalence before the further identification of the RV kernel with the degree-one principal relation. It does not claim the principal-ideal, normalized coefficient, full function-space or Fubini/change-of-variables conclusions of7.11-7.15.

The18-module/67-export batch passed actual source compilation, one complete1,109-line new type/axiom review and one affected Library build (11,998 jobs including cached dependencies). The checked local boundary is1,197 source modules plus Library with3,750 exports. Earlier proofs were not audited again. The last remote checkpoint remains1,179 modules at4129962fe5b6910593999c53f0dbcc1347d050bf; the next is due around1,279.


## Almost-everywhere function integration and one-coordinate descent

`selected_family_canonical_integral_ae_independent` and `aeRVVolumeFunctionIntegral` establish the positive homogeneous integral on the actual quotient by equality outside a definable VF-small base set. The density graph commutes with the full selected VF lift by a genuine volume bijection; the arithmetic degree identification with the canonical realization is explicit. Thus the integral is the already proved integration equivalence of the actual full VF lift, and cofull base removal proves representative independence.

`SelectedVFVolumeFamily.headIntegral` is the actual one-head contraction family, with the old selected coordinates followed by the new head tag, and the original density retained. `selected_family_head_integral_comparison` proves independence of pointwise representatives and of the chosen head preparation. `selected_family_head_integral_ae_comparison` proves independence for the larger almost-everywhere relation; `aeRVVolumeFunctionHeadIntegral` is the resulting quotient map. The new coordinate-order convention remains explicit. The pointwise identification with the canonical unary fibre integral, the comparison of iterated and total integrals, arbitrary coordinate projections, semimodule operations and ordinary degree-zero coefficients are still required for the complete7.11.

For the almost-everywhere descent, generic head comparison is converted to a finite formula-witness cover by checked saturation compactness. Its complement is an original-base definable pure VF set with no independent tuple, hence has smaller dimension. New original-Gamma row realization lemmas retain the full geometric charts, center algebraicity and exact blowup-chain lengths through all finite internal context extensions. This proves the descent without adding a Section5.8 hypothesis.

This14-module/43-export batch passed actual source compilation, one complete883-line new type/axiom review and one affected Library build (12,012 jobs including cached dependencies). The checked local boundary is1,211 source modules plus Library with3,793 exports. Earlier exports were not audited again. The remote remains1,179 modules at4129962fe5b6910593999c53f0dbcc1347d050bf; the next backup is due around1,279.


## Positive homogeneous prefix Fubini and coordinate pushforwards

`aeRVVolumeFunctionAppendedIntegral` descends the coefficient-first integral to the actual almost-everywhere function quotient. The reverse coordinate-chart comparison retains the original density on both sides and uses a common inverse permutation. This does not assert an unsigned isomorphism between different coordinate orders.

`native_coordinate_family_canonical_integral_formula` computes a literal native family integral by any specified standard contraction, without another density-graph insertion. Its appended-order counterpart computes the coefficient-first integral by a specified identity-order contraction. `appendedHeadIntegralVolumeIso` is an actual volume isomorphism between the successive head/tail contraction object and the whole concatenated contraction object, with literally equal volume tuples and retained density. It proves `ae_rv_volume_function_appended_head_fubini`. Induction gives `ae_rv_volume_function_appended_prefix_fubini` for any number of initial VF coordinates, leaving a nonempty base. Heterogeneous equality records the arithmetic total-degree identification.

VF coordinate permutations act on actual selected families and on their pointwise and almost-everywhere quotients. The old RV row is identified by a genuine full volume isomorphism in the retained finite VF parameter context. Pure VF exceptional sets retain their dimension under the actual definable permutation bijection. `aeRVVolumeCoordinatePushforward` uses the actual retained/complementary enumerations of an arbitrary nonempty coordinate projection, followed by prefix integration. Its total integral equals total integration in that split order. Comparing these values across projections still requires the explicit final RV coordinate normalization; the full7.11, semimodule structure and ordinary degree-zero coefficient cases are not claimed complete.

This15-module/49-export batch passed actual source compilation, one complete864-line new type/axiom review and one affected Library build (12,027 jobs including cached dependencies). The checked local boundary is1,226 source modules plus Library with3,842 exports. Earlier exports were not audited again. The remote remains1,179 modules at4129962fe5b6910593999c53f0dbcc1347d050bf; the next backup is due around1,279.


## Positive homogeneous coordinate Fubini with explicit global coordinates

`positive_coordinate_volume_fubini` and `positive_set_coordinate_volume_fubini` compare the actual iterated integrals for arbitrary nonempty coordinate projections and subsets, for positive homogeneous functions on the actual almost-everywhere quotient. `normalizedCoordinateVolumeIntegral` first computes the actual coordinate pushforward and its appended total integral. `coordinateVolumeIntegralNormalizer` then performs only the explicitly specified arithmetic degree reindexing, appended-to-canonical RV permutation, and inverse VF block permutation. `normalized_coordinate_volume_integral_eq_total` proves that this result is the original canonical total integral. The normalizer does not assume any integral equality.

The key geometric input is `permutedNativeContractionVolumeIso`: one actual ordered contraction program, viewed on the original and permuted VF sources, gives selected RV tuples related by exactly the corresponding VF block permutation and identical retained densities. `ae_rv_volume_function_integral_permute_base` proves this covariance on the almost-everywhere quotient, and its inverse restores the original coordinate order. `selectedIntegralNormalizationIso` gives a genuine volume isomorphism after the appended tuple has explicitly been reindexed; `ae_rv_volume_integral_from_appended` identifies the two integral conventions. No unsigned individual permutation or unsigned positive-product commutativity is asserted.

This establishes the positive homogeneous coordinate Fubini comparison with coordinate labels made explicit. The complete paper7.11 function-space result still requires the full pointwise fibre-integral identification, the semimodule operations and ordinary degree-zero coefficients. The inverse-Jacobian family construction for7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This13-module/37-export batch passed actual source compilation, one complete610-line new type/axiom review and one affected Library build (12,040 jobs including cached dependencies). The checked local boundary is1,239 source modules plus Library with3,879 exports. Earlier exports were not audited again. The remote remains1,179 modules at4129962fe5b6910593999c53f0dbcc1347d050bf; the next backup is due around1,279.


## Addition of almost-everywhere volume functions and additive integration

`aeRVVolumeFunctionAddCommMonoid` equips the actual positive homogeneous almost-everywhere quotient with pointwise addition, represented by genuine tagged family coproducts, and with the empty-family zero. `aeRVVolumeFunctionIntegralAddHom` proves that the canonical integral is an additive homomorphism. These are operations on actual definable families and their existing AE relation.

`DefinableVFVolumeFamily` allows an arbitrary definable RV volume map, finite after both the VF base and volume tuple have been fixed. `toSelected` retains its volume graph as extra RV labels; `selectionRowIso` identifies every row with the original volume object. This permits actual tagged coproducts without assuming that their glued volume map is a single fixed coordinate selection. The union of the two original VF-small exceptions proves well-definedness of addition.

For integration, the full VF realization forgets the redundant graph labels by an actual definable bijection preserving every VF coordinate and the original density. `definableVolumeFamilyLiftCoprodBijection` and `selectedFamilySumLiftBijection` identify the realization of the family sum with the actual VF coproduct. The checked additive integration equivalence then proves `selected_family_canonical_integral_add`. The empty realization proves preservation of zero. Arithmetic degree equalities are explicit; no individual unsigned coordinate permutation is assumed volume preserving.

This completes the additive part of positive homogeneous function integration. Scalar operations, all graded coefficients including ordinary degree zero, full pointwise fibre-integral identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This18-module/75-export batch passed actual compilation, one complete1,022-line new type/axiom review and one affected Library build (12,058 jobs including cached dependencies). The checked local boundary is1,257 source modules plus Library and3,954 exports. Earlier exports were not audited again. Remote backup remains1,179 modules; the next backup is due around1,279.


## Ordinary coefficient semimodules and linear integrals

`aeRVVolumeFunctionOrdinaryModule` gives each positive homogeneous AE volume-function quotient its actual semimodule structure over ordinary RV[0] common-blowup classes. Multiplication by a coefficient is represented by `SelectedVFVolumeFamily.prodZero`, an actual finite RV factor. Its selected coordinates and density are exactly those of the positive family; no density is assigned to the ordinary coefficient. `volumeFamilyZeroProductRowIso` proves the genuine fibre product formula, and coefficient isomorphisms extend to each named fibre. The AE construction keeps the original small exceptional set.

`volumeFamilyZeroProductLiftBijection` identifies the actual full VF realization with its ordinary-coefficient VF product, fixing every VF coordinate and retaining the density. The previously checked geometric coefficient-product integration theorem proves `ae_rv_volume_function_integral_zero_coefficient`. Together with addition, this gives `aeRVVolumeFunctionIntegralOrdinaryLinearMap`.

`ordinaryVolumeCoefficientExtend` is the actual coefficient-extension semiring homomorphism, and `positiveVolumeClassExtendSemilinearMap` records compatibility of positive volume classes with this extension. The actual permuted-row isomorphisms then prove `aeRVVolumeFunctionPermuteBaseOrdinaryLinearMap`: VF coordinate reindexing is linear over ordinary coefficients. This assertion concerns functions and does not assert an unsigned individual volume-coordinate isomorphism.

This completes the ordinary-coefficient semimodule and linearity part for positive homogeneous functions. Positive-degree coefficient actions, degree-zero-valued functions, full pointwise fibre-integral identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This14-module/43-export batch passed actual source compilation, one complete597-line new type/axiom review and one affected Library build (12,072 jobs including cached dependencies). The checked local boundary is1,271 source modules plus Library and3,997 exports. Earlier exports were not audited again. Remote backup remains1,179 modules; the next backup is due around1,279.


## Positive coefficient products on AE functions

`aeRVVolumeFunctionPositiveCoefficientProduct` constructs actual multiplication by a positive common-blowup coefficient class. The underlying family is the Cartesian product with the coefficient RV domain. Its old domain labels remain first, while `volumeFamilyConstantVolumeMap` places the coefficient volume tuple first and the original family tuple second; its density is the product of the two original densities. Finiteness at a fixed volume tuple follows from the two actual finite-fibre conditions.

`volumeFamilyPositiveCoefficientRowIso` and `selectedVolumeFamilyLeftProductRowIso` identify every fibre with the genuine coefficient-first RV volume product. The label blocks are swapped by an actual definable map, while the volume tuple and density agree literally. Existing common-blowup product compatibility proves descent in both the coefficient and AE function, using the original small exceptional set.

`aeRVVolumeFunctionPositiveCoefficientBiadditive` proves additivity and preservation of zero in both arguments on actual AE function classes. `positive_volume_class_extend_product` records genuine parameter-extension compatibility. `ae_rv_volume_positive_coefficient_assoc` proves associativity of two positive coefficient actions, with only the arithmetic coefficient-degree equality expressed by HEq. No volume-coordinate permutation or unsigned positive-product commutativity is used.

Positive-coefficient compatibility with the canonical/appended integral remains open: the canonical VF realization orders the original VF base before the coefficient realization, and this must be connected by explicit volume-coordinate identifications. Mixed ordinary/positive scalar coherence, ordinary degree-zero-valued function spaces, full pointwise fibre identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 also remain open.

This9-module/27-export batch passed actual source compilation, one complete410-line new type/axiom review and one affected Library build (12,081 jobs including cached dependencies). The checked local boundary is1,280 source modules plus Library and4,024 exports. Earlier exports were not audited again. This reaches the next roughly100-module backup interval after the1,179-module remote checkpoint.


## Actual coefficient-first VF realizations and integral covariance

`positive_vf_volume_integral_permutation_covariance` proves covariance of the actual positive integration equivalence for an arbitrary VF volume object and arbitrary density: permuting the VF coordinates permutes the resulting RV volume tuple by exactly the same permutation, retaining the density. `permutedRawContractionVolumeIso` proves the literal coordinate statement on an actual ordered contraction program. The density graph and native-domain charts extend it from retained coordinate densities to arbitrary original forms through genuine VF-preserving volume bijections.

`SelectedVFVolumeFamily.appendedFullLift` is the actual coefficient-first VF realization: its front VF block realizes the selected RV tuple, and its remaining VF block is the original family base. `selected_family_appended_integral_full_lift` proves that integration of this actual object is the appended family integral. The proof uses the explicit VF covariance, arithmetic degree identifications and the established appended/canonical RV coordinate chart. It does not identify an unsigned coordinate permutation with a volume-preserving map. `mem_appended_family_full_lift` and `appendedFullLift_density` give the literal carrier and original-density formulas.

`DefinableVFVolumeFamily.appendedFullLift` handles arbitrary definable volume maps. It forgets the selected presentation's redundant graph labels through `definableVolumeFamilyAppendedSelectionBijection`, an actual VF-preserving volume bijection. `mem_definable_appended_family_lift` gives its exact carrier: the original base point belongs to the family, and the front VF tuple realizes its volume map. The original density is retained. `vfPreservingLabelImageBijection` packages this genuine geometric label-image construction with a proved finite-RV-fibre condition.

This closes the earlier open bridge identifying the coefficient-first family integral with an actual full VF realization. Positive-coefficient integral compatibility still requires its product comparison with a coefficient VF lift. Mixed scalar coherence, degree-zero-valued functions, full pointwise fibre identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This12-module/38-export batch passed actual source compilation, one complete525-line new type/axiom review and one affected Library build (12,093 jobs including cached dependencies). The checked local boundary is1,292 source modules plus Library and4,062 exports. Earlier exports were not audited again. Remote backup remains1,280 modules at0db36604e7c1f8de0fe04c767fa528f9084abafd; the next backup is due around1,380.


## Positive coefficient compatibility of actual appended integration

`ae_rv_volume_appended_integral_positive_coefficient` proves that the actual coefficient-first AE integral preserves multiplication by a positive common-blowup coefficient class. Its HEq changes only the arithmetic expression for the total degree. The selected-family representative formula is `selected_family_appended_integral_positive_coefficient`.

The geometric proof is `selectedPositiveCoefficientAppendedLiftBijection`. The full VF realization has blocks consisting of the coefficient realization, the original family-volume realization, and the original VF base. `appendedCoefficientLiftProductMap` swaps only the RV domain-label blocks, fixes every VF coordinate, is genuinely bijective, and preserves the original product density. `appendedCoefficientLiftProductBijection` therefore identifies it with the actual Cartesian product of the coefficient VF lift and family realization, with the explicit arithmetic degree cast. The checked7.10 integration-product theorem and actual coefficient-lift identity then give the integral formula. No unsigned VF permutation is assumed volume preserving.

`aeRVVolumeFunctionAppendedIntegralAddHom` and `aeRVVolumeFunctionAppendedIntegralOrdinaryLinearMap` establish additive and ordinary-RV[0]-linear integration in this same coefficient-first convention. `canonicalFromAppendedVolumeOrdinaryLinearEquiv` proves that the explicit canonical/appended coordinate identification is ordinary linear, using actual coproduct and degree-zero product charts.

This completes the positive-coefficient integral compatibility previously left open. Mixed ordinary/positive scalar coherence, full graded function-space assembly including ordinary degree-zero-valued functions, full pointwise fibre-integral identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This13-module/29-export batch passed actual source compilation, one complete417-line new type/axiom review and one affected Library build (12,106 jobs including cached dependencies). The checked local boundary is1,305 source modules plus Library and4,091 exports. Earlier exports were not audited again. Remote backup remains1,280 modules at0db36604e7c1f8de0fe04c767fa528f9084abafd; the next backup is due around1,380.


## Ordinary degree-zero-valued AE integration and mixed scalar coherence

`AEOrdinaryRVVolumeFunction` is the genuine AE quotient of finite ordinary RV[0] row families, with no assigned row density. `aeOrdinaryRVVolumeFunctionIntegral` integrates the actual original family domain with unit VF form; `aeOrdinaryRVVolumeFunctionIntegralAddHom` proves additivity for actual pointwise tagged coproducts and the literal empty family.

Its descent is unconditional under the recorded BaseContext assumptions. Equality of ordinary row classes gives actual finite RV isomorphisms over the term closure of the original real base and each VF tuple. `gamma_rv_map_graph_of_term_closure` eliminates those term parameters. `ordinary_volume_family_uniform_bijection` then uses the already checked Section6 `gamma_mixed_fibre_uniformity` over the original real base and empty Gamma parameter set to obtain one genuine definable bijection preserving every VF coordinate. Its Jacobian and the unit densities are checked by `VFVolumeBijection.of_preserving_vf_and_density`. Removing a VF-small base exception preserves the full VF volume class because RV labels add no VF dimension. This proves `ordinary_volume_full_class_eq_of_ae` and the actual quotient realization/integral, without applying the excluded empty-selected case of7.5, assuming field generation for a term context, or adding a Section5.8 hypothesis.

`ae_rv_volume_positive_coefficient_smul_left` and `ae_rv_volume_positive_coefficient_smul_right` prove both mixed ordinary/positive scalar compatibilities on actual AE functions. `aeRVVolumeFunctionPositiveCoefficientOrdinaryBilinearMap` packages the positive-coefficient action as a genuine bilinear map over ordinary RV[0]. The coefficient commutative semiring is proved by the actual swap of two degree-zero finite RV factors; positive-product commutativity is not asserted.

Full graded assembly, scalar and positive-coefficient products involving ordinary-valued functions, full pointwise fibre-integral identification,7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This19-module/51-export batch passed actual source compilation, one complete694-line new type/axiom review and one affected Library build (12,199 jobs including cached dependencies). The checked local boundary is1,324 source modules plus Library and4,142 exports. Earlier exports were not audited again. Remote backup remains1,280 modules at0db36604e7c1f8de0fe04c767fa528f9084abafd; the next backup is due around1,380.


## Ordinary function scalar compatibility and the finite graded integral

`aeOrdinaryRVVolumeFunctionModule` gives the genuine ordinary RV[0] scalar action on ordinary-valued AE functions. It is represented by an actual finite RV factor. `ordinaryVolumeScalarRealizationBijection` identifies its full unit-density VF realization with the Cartesian product by that factor's VF lift. The checked product-integration theorem proves `ae_ordinary_rv_volume_integral_smul`, packaged as `aeOrdinaryRVVolumeFunctionIntegralLinearMap`.

`aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct` multiplies an ordinary-valued AE function by an actual positive common-blowup coefficient. The row class is its ordinary fibre class acting on the extended positive coefficient. `aeOrdinaryRVVolumeFunctionPositiveCoefficientBilinearMap` proves ordinary bilinearity, and `ae_ordinary_positive_coefficient_assoc` proves compatibility with a further positive coefficient action.

`ordinaryPositiveCoefficientLiftBijection` is the actual coefficient-first VF comparison: it fixes every VF coordinate, swaps only the RV label blocks, preserves the original positive coefficient density, and introduces no density on the ordinary family. Thus `ae_ordinary_positive_coefficient_appended_integral` proves the genuine integral-product formula. Its HEq changes only the arithmetic expression of the total degree.

`GradedAEVolumeFunction` now assembles ordinary degree zero and all positive homogeneous degrees as a finite direct sum. `gradedAEVolumeIntegralOrdinaryLinearMap` integrates this full space linearly over ordinary RV[0], placing the component of coefficient degree j over VF base arity n+1 into total degree n+j+1. Positive components use the checked coefficient-first integral with an explicit arithmetic degree identification. This does not yet assert a semimodule over the full graded coefficient semiring.

The remaining7.11 work is the full graded coefficient action/module and integral linearity over it, together with full pointwise fibre-integral identification and the remaining degree-zero coordinate Fubini bridge.7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This17-module/48-export batch passed actual source compilation, one complete709-line new type/axiom review and one affected Library build (12,216 jobs including cached dependencies). The checked local boundary is1,341 source modules plus Library and4,190 exports. Earlier exports were not audited again. Remote proof backup remains1,280 modules; the next proof backup is due around1,380. The checkpoint branch separately contains the checked CI optimization and cancellation-cache fixes. Its current head45231668689d9b6c91f1872d0d5f8acfb7eebb91, tree fd771c5d3e9fdea5bf97857a327b9d6eb3a73ae8, is the parent of the next proof backup. CI run43696538789 was pending at publication; no warm-cache runtime or remote CI success is claimed.


## Full graded function linearity and ordinary first-head integration

`gradedAEVolumeFunctionModule` supplies the actual action of the full graded common-blowup coefficient semiring on the finite graded AE function space. Its component action covers ordinary/ordinary, ordinary/positive, positive/ordinary and positive/positive degrees. The genuine row products, previously checked bilinearity and associativity prove all action laws. `gradedAEVolumeIntegralLinearMap` is the resulting integral linear over the full graded coefficient semiring; `graded_ae_volume_integral_smul` proves its actual product formula. No new action or integral compatibility hypothesis is assumed.

`OrdinaryVFVolumeFamily.headIntegral` contracts the unit-density VF realization's density graph and selects exactly the new head tag. Finite-label head preparation with zero old selected coordinates proves actual finiteness. This does not invoke an empty-selected version of Lemma7.5. `ordinaryHeadIntegralVolumeIso` identifies the first head tag followed by the remaining contracted VF tags with the original full VF contraction. `ordinary_family_appended_head_fubini` gives the genuine iterated integral identity; its HEq changes only the arithmetic expression of total degree.

`ordinary_volume_family_bijection_fixing_vf` retains all VF coordinates in the ordinary finite-fibre uniformity construction. It gives original-Gamma geometric head comparisons at generic retained tuples. A finite formula-witness cover proves `ordinary_family_head_integral_comparison_of_pointwise`, including independence from the chosen head preparation. The input here is pointwise equality of ordinary rows. Extending this conclusion to ordinary source presentations equal outside a VF-small exception remains open and is not counted as proved.

The remaining7.11 work is ordinary AE head descent and the full pointwise fibre-integral identification, followed by assembly of the full graded coordinate Fubini statement.7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This13-module/40-export batch passed actual source compilation, one complete658-line new type/axiom review and one affected Library build (12,229 jobs including cached dependencies). The checked local boundary is1,354 source modules plus Library and4,230 exports. Earlier exports were not audited again. Remote proof backup remains1,280 modules; the next proof backup is due around1,380. The CI optimization head is45231668689d9b6c91f1872d0d5f8acfb7eebb91 (treefd771c5d3e9fdea5bf97857a327b9d6eb3a73ae8), the required parent of the next proof backup. Its first cold-cache run43696538789 was still building when last inspected; no warm-cache runtime or remote CI success is claimed.


## Finite-row geometry for ordinary head descent

`gamma_ordinary_unary_prepared_volume_slice_witness` and `gamma_ordinary_unary_prepared_volume_comparison_with_geometry` prove the first-volume-coordinate unary comparison using actual finite-label slice lift charts with unit VF Jacobian. There are zero old selected volume coordinates, and the output has the sole new head volume tag. This argument uses the checked unary common-schema geometry and does not assume an empty-selected version of Lemma7.5.

`gamma_finite_row_isomorphism_formula_witness` promotes actual finite Gamma row isomorphisms to chart witnesses with the given endpoint formulas. `generic_finite_isomorphism_preparation_in_context` prepares a finite witness cover so that every essential prepared RV cell carries a valid recoded chart. Nonzero prepared cells contain actual inverse images generic over the original VF parameter field. The original Gamma formulas and their full graph certificates are retained.

`gamma_indexed_ordinary_row_bijection` uniformizes these charts to an actual bijection fixing every RV index coordinate. `indexed_ordinary_label_equiv_volume` proves preservation of the complete base volume tuple when the fibre has ordinary degree zero. `gamma_indexed_ordinary_unit_volume_comparison` realizes the resulting unit-density volume isomorphism in a genuine small containing context, with its original-Gamma graph. `gamma_unit_coordinate_density_iso` supplies the exact chart between a retained unit density and the literal unit form in degree one.

The finite-membership and partition preparation lemmas also preserve original-Gamma certificates on the global special chain and all restricted pieces, without a VF/Gamma generation assumption on an arbitrary containing term context.

These are proved geometric prerequisites for ordinary AE head descent. The remaining assembly must restrict the prepared ordinary indexed objects to nonzero base-volume indices, compare both specified unary contractions, and then use the checked finite formula-witness descent. Ordinary AE head descent and the full pointwise fibre-integral identification are not yet asserted.7.12 and the principal-relation/normalized-coefficient conclusions of7.13-7.15 remain open.

This16-module/30-export batch passed actual source compilation, one complete1,228-line new type/axiom review and one affected Library build (12,245 jobs including cached dependencies). The checked local boundary is1,370 source modules plus Library and4,260 exports. Earlier exports were not audited again. Remote proof backup remains1,280 modules; the next proof backup is due around1,380. Its required parent is CI optimization head45231668689d9b6c91f1872d0d5f8acfb7eebb91, treefd771c5d3e9fdea5bf97857a327b9d6eb3a73ae8. The first cold-cache CI run43696538789 was still building when last inspected; no warm-cache runtime or remote CI success is claimed.


## Ordinary unary comparison from generic row isomorphisms

`gamma_ordinary_unary_raw_comparison_from_generic_geometry` proves actual original-Gamma common forward volume blowups of two specified raw unary finite contractions. Its inputs are generic finite ordinary-row isomorphism formula witnesses, literal empty old-volume rows, matching native source sets and retained unit densities. The preparation and all volume charts are constructed; no VF/Gamma generation condition is imposed on the containing term context.

The proof restricts ordinary indexed objects to nonzero base-volume indices. Every essential volume label lies over one of those indices. Formula-chart uniformity gives an actual unit-density volume isomorphism on the restriction, and the containing-essential restriction charts restore the whole volume objects. Unit-density labels are retained through the actual prepared indexed presentation.

The zero-old-selected unary prepared comparisons compare both specified contractions to these indexed objects. Parameter-extension label charts retain original-Gamma geometry. Finally the empty-selected volume tuple is identified with the ordinary normalized tuple, and the checked first-volume normalization charts recover the raw finite contraction endpoints. No empty-selected version of Lemma 7.5 is assumed.

Ordinary AE head descent still requires applying this comparison to the generic rows of the frozen head fibres and assembling the existing head presentation charts. Full pointwise fibre-integral identification, 7.12 and the principal-relation/normalized-coefficient conclusions of 7.13–7.15 remain open.

This 13-module/18-export batch passed actual source compilation, one complete 893-line new type/axiom review and one affected Library build (12,258 jobs including cached dependencies). The checked local boundary is 1,383 source modules plus Library and 4,278 exports. Earlier exports were not audited again. The next authorized proof backup uses CI head 45231668689d9b6c91f1872d0d5f8acfb7eebb91 as parent; the published CI cache and Section 6 compilation changes are preserved. No measured warm-cache CI runtime is claimed.


## Ordinary AE first-head integration and Fubini

`ordinary_family_head_integral_comparison_of_ae` proves that ordinary RV[0]-valued families equal outside a definable VF-small set have equal positive-valued first-head integrals outside a definable VF-small set in the retained base. Both head preparations are arbitrary. `aeOrdinaryRVVolumeFunctionHeadIntegral` therefore defines the actual AE quotient map, and `ae_ordinary_rv_volume_function_head_integral_representative` identifies its value for every chosen head preparation.

The proof appends the genuine unit density by an actual definable bijection preserving every VF coordinate and restricts this chart to each row over the original base plus its VF tuple. Ordinary row-class equality gives an actual finite Gamma row isomorphism. It is promoted to a finite formula chart with the given endpoint schemata. A uniform formula bound also covers zero selected coordinates.

At a generic frozen VF tail, generic unary points give generic full VF tuples by algebraic independence over the actual generated tuple field. The previously checked ordinary unary comparison gives common forward blowups of both raw unary contractions, with full original-Gamma geometry. The head fibre presentation charts recover the specified head objects. A finite formula-witness cover then descends this comparison to one original-base definable small exception. This avoids assuming that an arbitrary frozen containing term context is VF/Gamma generated. The chosen quotient map retains the established generation assumption only on the original global context.

`ae_ordinary_rv_volume_function_appended_head_fubini` proves total Fubini on this actual ordinary AE quotient using the already checked presentation-level contraction concatenation. Its heterogeneous equality records only the arithmetic total-degree identification. Together with the positive homogeneous result, first-head Fubini is now established on every homogeneous coefficient component, including ordinary degree zero.

Assembly on the full finite graded function space and full pointwise fibre-integral identification remain to be completed. 7.12 and the principal-relation/normalized-coefficient conclusions of 7.13–7.15 remain open.

This 12-module/18-export batch passed actual source compilation, one complete 587-line new type/axiom review and one affected Library build (12,270 jobs including cached dependencies). The checked local boundary is 1,395 source modules plus Library and 4,296 exports. Earlier exports were not audited again. The durable source backup is the 1,383-module checkpoint 8d0d1c1f03c5377acf3bc0d195bbb8435389f373, tree a36ad857a8d827f25adc886602472727ea19d499. The next proof backup is due around 1,483 modules. Its CI optimization files are preserved; the first canceled cold build successfully saved its completed project modules, and the next run restored the cache. No completed warm-runtime measurement is claimed.


## Full finite graded first-head Fubini

`gradedAEVolumeHeadIntegral` is the actual zero-preserving first-head map on the full finite graded AE function space. Degree zero uses the ordinary AE head integral, and each positive homogeneous degree uses the checked positive head map. Empty-domain contraction geometry proves zero preservation in every component. The dependent finite sum therefore defines the map independently of a finite support bound.

`graded_ae_volume_head_integral_component` identifies every degree j+1 output with the genuine head integral of input degree j. `graded_ae_volume_head_integral_zero_component` proves that its ordinary output component vanishes. These are exact formulas on the actual AE quotients.

`graded_ae_volume_head_fubini` proves the exact first-head Fubini equality for arbitrary finitely graded AE functions, including the ordinary component. It combines the homogeneous contraction-based Fubini proofs, the established additive total integral and the finite support decomposition. Arithmetic degree identifications are checked by the homogeneous total-degree equality; no coordinate permutation or unsigned Jacobian identity is inserted.

The total integral is already linear over the full graded coefficient semiring. This head-map construction is packaged as a ZeroHom; partial-head additivity or full coefficient linearity is not asserted here. Full pointwise fibre-integral identification, 7.12 and the principal-relation/normalized-coefficient conclusions of 7.13–7.15 remain open.

This 6-module/16-export batch passed actual source compilation, one complete 258-line new type/axiom review and one affected Library build (12,276 jobs including cached dependencies). The checked local boundary is 1,401 source modules plus Library and 4,312 exports. Earlier exports were not audited again. The durable proof backup remains the 1,383-module checkpoint 8d0d1c1f03c5377acf3bc0d195bbb8435389f373; the next source backup is due around 1,483 modules.

CI performance is now measured: GitHub Actions run 43701336994 on that published 1,383-module checkpoint passed the complete build and all section audits. Its creation time was 09:52:33 UTC and final status time 10:02:11 UTC on November 15, 2026, an elapsed 578 seconds (9 minutes 38 seconds). It includes 103 new Section 7 modules since the preceding proof checkpoint. The first canceled cold build saved its completed project modules, and this run restored and saved the project cache successfully. Local receipts record the remote result. The published optimization retains every headline type/axiom audit while reusing Lake-validated compilation artifacts and avoiding the duplicate Section 6 isolated compilation.


## Full graded prefix Fubini and inverse-Jacobian transport

`gradedAEVolumePrefixIntegral` integrates any VF prefix while retaining a nonempty VF base. It is the actual composition of the checked full graded head maps, with zero preservation. `graded_ae_volume_prefix_fubini` proves exact equality of its total integral with the original total integral. `graded_ae_volume_prefix_integral_of` identifies each homogeneous input with its actual iterated homogeneous head integral. The positive prefix map is the existing selected-family prefix map; ordinary inputs use their first ordinary head and then the positive prefix map. Only arithmetic degree identifications are heterogeneous.

`inverseJacobianVFVolumeForm` is the literal product of the definable inverse-Jacobian density and the original form pulled back by the inverse bijection. The already checked total Jacobian map replaces exceptional zero values by one, so the form is everywhere definable and nonzero. `mixed_inverse_jacobian_density_balance_ae` proves the inverse/forward product law almost everywhere using the actual chain rule and the identity Jacobian. `preserves_inverse_jacobian_vf_volume` proves measure preservation for this actual form.

`inverseJacobianVFVolumeBijection` constructs a genuine volume-preserving bijection from a positive VF volume object to its inverse-Jacobian transform. `inverse_jacobian_vf_volume_integral` gives the corresponding equality under the established integration equivalence. This proves the object-level change-of-variables bridge; the full function-level assertion of Proposition 7.12 is not yet asserted.

`mixedVFBaseMap` changes only the VF tuple of a family by a specified definable base bijection and retains all RV labels. Its actual image map is a bijection, and selected RV fibre finiteness follows from the inverse base tuple. `SelectedVFVolumeFamily.pushforwardBase` constructs the unweighted family pushforward, with its literal inverse-base fibre and transported density formulas. The remaining function-level bridge must apply the inverse base-Jacobian correction, identify the full lift Jacobian with the base Jacobian, and descend through AE representatives.

Full pointwise fibre-integral identification, arbitrary-coordinate graded comparison and the principal-relation/normalized-coefficient conclusions of 7.13–7.15 remain open. Ordinary RV[0] and the accepted nonempty-selected scope of Lemma 7.5 are retained.

This 6-module/24-export batch passed actual source compilation, one complete 460-line new type/axiom review and one affected Library build (12,282 jobs including cached dependencies). The checked local boundary is 1,407 source modules plus Library and 4,336 exports. Earlier exports were not audited again. The durable proof backup is still the 1,383-module checkpoint 8d0d1c1f03c5377acf3bc0d195bbb8435389f373; the next proof backup is due around 1,483 modules. GitHub Actions run 43701336994 passed the published checkpoint and every section audit in an observed 9 minutes 38 seconds after the CI cache and duplicate-compilation fixes. No new push was made for local receipt-only updates.


## Actual family Jacobian transforms and base-Jacobian agreement

`SelectedVFVolumeFamily.jacobianPushforward` constructs the actual positive selected-family Jacobian transform along a definable VF base bijection. Its domain is the genuine image family, its selected RV coordinates are unchanged, and its density is the transported original form multiplied by the inverse base-Jacobian density. `jacobianPushforward_density` is the literal value formula at every image point. This construction does not yet assert AE representative independence or preservation of the full lifted integral.

The base Jacobian uses an actual mixed presentation of the pure VF map with an empty RV tuple. The empty-graph map is a definable bijection, and the inverse-Jacobian density pulls back to a nonzero definable form on the pure VF target. No additional parameter names or formal Jacobian predicates are introduced.

`has_mixed_vf_jacobian_base_product` proves that attaching fixed RV labels leaves the base Jacobian unchanged. `mixed_vf_base_jacobian_eq` compares the actual family map with this ambient map whenever both Jacobians are defined. `mixed_vf_base_jacobian_density_at_generic` supplies the actual equality of the definable Jacobian densities at every generic family point using the checked differentiability and nonzero-Jacobian theorems.

`vf_almost_everywhere_maps_eq_of_generic` descends generic agreement of actual definable maps to one original-base definable VF-small exception, by the complement of the definable diagonal and the VF transcendence-degree bound. `mixed_vf_base_jacobian_density_agreement_ae` applies it to the actual family and base-Jacobian density maps. `VFAlmostEverywhere.at_independent` provides the converse use of an already witnessed small exception at a generic point.

The remaining change-of-variables work is to compare the inverse densities, lift the corrected family map while fixing the coefficient VF tags, and descend through AE function representatives. Full pointwise fibre-integral identification, arbitrary-coordinate graded comparison and the principal-relation/normalized-coefficient conclusions of 7.13–7.15 remain open.

This 7-module/20-export batch passed actual source compilation, one complete 375-line new type/axiom review and one affected Library build (12,289 jobs including cached dependencies). The checked local boundary is 1,414 source modules plus Library and 4,356 exports. Earlier exports were not audited again. The durable proof backup remains the 1,383-module checkpoint 8d0d1c1f03c5377acf3bc0d195bbb8435389f373; the next proof backup is due around 1,483 modules. Its GitHub Actions run 43701336994 passed the complete build and every section audit in the observed 9 minutes 38 seconds after the CI optimization.


## Inverse family densities and full lifted Jacobian change of variables

The inverse mixed-family Jacobian density now agrees with the inverse pure-base Jacobian outside one actual original-base VF-small exception. The proof cancels the established nonzero forward density from the two actual inverse/forward balance laws, first at generic points and then on a definable cofull set. `selected_family_jacobian_pushforward_preserves_volume` proves the volume equation for the actual corrected mixed family.

`selectedTailLiftMap` realizes an actual RV-label-preserving map while fixing every additional coefficient VF coordinate. It is bijective whenever the original map is bijective. General raw mixed-domain product AE and Jacobian arguments avoid assuming finite RV fibres of an intermediate family. Restriction to the literal selected-tail realization gives `selectedFamilyJacobianFullLiftBijection`, a genuine full volume-preserving bijection from `F.fullLift` to the corrected family's full lift.

`selected_family_jacobian_canonical_integral` proves equality of the literal positive-family canonical integrals under this actual Jacobian transform. This closes the inverse-density and full-lift bridges previously recorded as open. AE function representative independence/descent, the full pointwise fibre-integral identification, arbitrary-coordinate full-graded comparison and the principal-relation/normalized-coefficient results7.13-7.15 remain open. Ordinary RV[0] and the accepted nonempty-selected scope of7.5 are unchanged.

This8-module/17-export batch passed actual source compilation, one complete412-line new type/axiom review and an affected Library build with12,297 jobs including cached dependencies. Only propext, Classical.choice and Quot.sound occur. The sealed local boundary is1,422 source modules plus Library and4,373 exports. Earlier proof batches were not audited again.
