# Section 5 reuse survey

Started November 10, 2026 (America/Los_Angeles).

| Source | Revision | License |
| --- | --- | --- |
| Special transformations | `9cc9760892092dd34cfad4a6dee655843c52f30c` | No root license file found; source attribution retained |
| ACVF-QE | `939346b0a99899e22a873479364e3cc5d142731c` | MIT |
| Mathlib | `56a005855ea17e0b0958f73ec801ae140b0a1679` | Apache-2.0 |
| Sequel starting checkpoint | `c8f4270` | Existing repository terms |
| Lean | `leanprover/lean4:v4.35.0` | Existing toolchain |

Read the predecessor's `LANGUAGE-ERRATA.md`, `Section4/STATUS.md` and
`Section5/STATUS.md`. Preserve named RV inversion and the single absorbing
point. The original old `CategoryLift` exports are conditional; prefer the
proved producers and repaired `Paper` exports rather than treating those
conditions as standing authorizations in this sequel.

## Selected reuse

- `Section5/Geometry.lean`: use actual `Point`, `key`, `SameRV`, hull and
  `IsRVPullback`; these compare RV classes, not only valuations.
- `Section5/Core.lean`: use actual definable `Map`, alternating
  `SpecialBijection`, its inverse, `Contractible`, `keyImage`,
  `contractionFun`, `contractionMap` and the unique definable contraction.
  No duplicate language, RV quotient or special-bijection definition.
- `Section5/GeneralExistence.lean`: `map_preparation_at_boundary` constructs
  actual special bijections in every finite mixed arity. It explicitly
  takes uniform vertical obstacles; discharge that premise with
  `Section5/VerticalObstacles.uniformVerticalObstacles` using genuine
  saturation and smallness. `Values.presentationValuation` and its proved
  compatibility remove a separately postulated valuation.
- `Section5/GammaExistence.lean`: `gamma_map_preparation_at_boundary` keeps
  full invariant locus/focus graphs over the original Gamma base, even when
  the working real code set is larger. Supply its logic and support inputs
  from `gammaLogicInput` and `gammaPolynomialSupportInput_of_fieldBase` in
  `GammaInvariantLogic` and `GammaPolynomialSupport`; never assume them.
- `GammaRestriction`: reuse chain graph and inverse graph theorems.
  `GammaBaseInputs.gammaPresentationInput` and
  `GammaGraphDefinable.real_specialize` offer the next common-presentation
  bridge. Their finite code sets must be combined without changing the
  final original-base graphs.
- Sequel `IntegrationSection3ACVF.CoordinatePartitions`: reuse the actual
  uniform coordinate-fibre partition for 5.2. Do not restate it as an
  assumed property of saturation.
- Pinned Mathlib: use `Function.Bijective`, `Equiv`, subtypes and ordinary
  function composition for the new quotient and relatively unary calculus.

The new 5.1 draft applies map preparation first to the target identity and
then to the transformed map. This avoids rebuilding polynomial preparation.
The new 5.2 quotient criterion proves exactly which remaining geometric
condition is necessary: inverse contractibility. It does not construct that
condition or complete 5.2.

No external proof source, HK theorem, referee claim or new citation is used
as an input. This batch imports existing declarations directly, with their
source attribution retained in the dependency. No source was ported from a
new external Lean project. Further reuse surveys are required before the
substantial 2-cell/relative-special construction, beyond these existing APIs.

## Build evidence

Fresh local dependency and proof compilation is pending. Toolchain version
was checked as Lean 4.35.0. Mathlib cache download was denied by the environment
proxy for `cache.mathlib.org`; an allowlist update was requested. A from-source
build of the actual prerequisite modules is running instead. The earlier
broad builds were deliberately interrupted (exit 130), retaining completed
artifacts. The target still inherits the foundation's whole-Mathlib import. Do not treat this
running build or source inspection as a passed proof certificate.

`GammaMapPresentation` now drafts the common-presentation bridge: take the
union of the three finite-code parameter sets, apply existing parameter
monotonicity, and retain the exact same source, target and function. The
set-level 5.1 wrapper has no presentation or code-set smallness premise.

## Checked first batch

All required pinned dependencies were built from source. The 72-head Section 5
build and complete type/axiom audit passed locally. The verifier prints proof
arguments and deeply nested types without omissions and records the full
types. Only the three permitted axioms occur. See VERIFICATION.json for exact
source and audit identities. Wider root integration remains a separate run.

The source focus is now constructed by composing the definable target-focus
section with the given inverse, selecting exactly those source RV cells
containing that point, and taking the VF coordinate as centre. Existing
first-order relation, graph and parameter-base operations prove the entire
locus and centre graphs over the original real base. The compatible-focus
induction and invariant Gamma certificate remain distinct obligations.


November11 chain batch: reused the pinned `RootConstruction.Chain` append,
alternation and last-kind calculus, `GammaInvariantLogic.gammaLogicInput`,
`GammaRestriction.GammaChainDefinable.graph` and `GammaExistence` preparation.
Actual types were inspected before reuse. The real/Gamma matching proofs
add no citation inputs or dependency revisions. `GammaParameters` intersection
is used on full invariant graphs, with injectivity of actual mixed codes
proved locally. The paper-open bridge uses this project's `PaperBalls` and
`GammaRadiusAtomicity.gammaBall`; it preserves the reversed value order and
does not replace equal RV classes by equal values. Root build and all161
full type/allowed-axiom checks passed; exact evidence in VERIFICATION.json.


November11 Lemma5.2 batch: inspected and applied this project's
`CoordinatePartitions.proposition_3_21` with its actual full-base scope,
saturation, small real base, ACVF00 and named nontrivial Gamma value.
`GammaFullBaseBridge` proves equivalence with predecessor GammaParameters
when the combined base has only names `Sum.inr γ`; the reverse direction
keeps the full invariant relation. The mixed tuple translations use pinned
`VerticalConstruction.pointValues`. Boundary preparation reuses
`gamma_map_preparation_at_boundary`, actual RV0/1 `membershipMap`,
`Chain.lastKind_allTagged` and `Centering.Chain.lastKind_append`.
The197-head complete audit and root/full project checks pass. All161 prior
types are unchanged; no dependency revision or outside citation changed.

For5.3, inspected pinned `RVCategories.RVHom` (both volumetric and
finite_volume_images are required), `PullbackLift.pullbackObject`, and
`FiniteImage.finite_rv_to_vf_relation_image`/`GammaBaseFiniteImage`.
The finite RV-to-VF image theorem is already formalized and requires
genuine saturation and a small real base, not VFFieldBase or a new
algebraicity reference. It will be specialized over finite original-base
support plus a fixed VF input; this proof remains in scratch.


November11 Remark5.3 batch: built and reused pinned
`Section5.PullbackLift.pullbackObject`, `rawKeyMap`, and the actual
`Section4.RVHom`/Category instances. `Map.descend` produces the quotient
map and its commuting square. `ValuedFieldExtension.exists_nontrivial_predV`
and `Balls.rv_eq_of_sub_lt` give two distinct points in every nonzero RV
cell; no legacy unregistered Sec3Fibre module is imported.
`FiniteImage.finite_rv_to_vf_relation_image` is used with actual normalized
saturation, finite real support and the fixed VF input. It gives finite
volume images without an internal code-set bound or an unproved
RV-algebraicity premise. The category morphisms and inverse laws compile;
all227 full type/allowed-axiom audits and root/project checks pass.

## Definition5.4 relative-special factorization

The pinned Special transformations FocusGeometry/Focus, Map and
SpecialBijection remain the actual notions. The fibre construction names
only the fixed complementary VF coordinates and restricts the focus locus
to the fibre RV hull. The checked original-Gamma preimage API in
Section5.GammaLiftRelation and monotonicity in Section3.GammaSupport retain
the original Gamma names. Mathlib Data.List.OfFn and Data.List.FinRange
(pinned revision in VERIFICATION.json, Apache2.0) are used only to prove the
exact RV-label order of the finite one-coordinate canonical factorization.
No additional mathematical theorem, citation or choice principle is used.
The local302-head section build/type/axiom audit, root build and full project
audits pass. Exact evidence and limitations are in VERIFICATION.json.

## Genuine uniform relative preparation

At the same pinned predecessor revision, RootFamily.focus supplies an actual
unary focus after restriction of each VerticalRootFamily to a coordinate
fibre. VerticalRootFamily.meanMap supplies uniform real definability;
finite_mean_child_bound proves the strict child-root bound. The local map
uses one-coordinate canonical steps and keeps every complementary VF
coordinate fixed. SpecialRelativeBoundary tracks actual fibre-chain
alternation through the finite induction.

The ordinary-ball inverse-slice proof and zero-obstacle relation argument
are adapted, with attribution in the sources, from checked
Section5.VerticalConstruction and Section5.Assembly. Their previous
compatible-global-chain inputs are replaced here by geometry proved from
actual unary fibre specials. uniformVerticalObstacles supplies the genuine
saturation/finite-root input; gammaPolynomialSupportInput_of_fieldBase keeps
coefficients in P.real. No field storing preparation existence, compactness
conclusion, saturation substitute or original-Gamma representative is used.
The separate Section4 chat's vertical work was inspected for comparison;
its geometric RelativeBijection structure was not imported as fibrewise
specialness. All392 local full type/axiom audits pass; integration evidence
and remaining5.5 obligations are recorded separately.

## Actual contraction sequences and natural lifts

The pinned primitive.restrict and extendBase APIs are used to retain actual
fibre-special chains and their last-kind boundaries. Real coordinate maps,
the original-Gamma invariant preimage/composition API and the pinned
RVObject/rawLift definitions supply the bridges. No new external result or
unproved Section4 cell assertion is used. All467 complete types/axioms pass;
the75 new types and actual data definitions were manually reviewed without
omissions. The natural lift is a proved definable bijection; its global
SpecialBijection bridge remains a separate open obligation.

## First-coordinate normalization and uniform partial contractions

At the unchanged pinned predecessor revision, Section4.RVIsoTools supplies
rvIsoOfVolumePreservingBijection. It is applied to the actual injective RV
coordinate duplication retaining all old labels, with exact volume equality
proved. Section4.RVWeightDimension.vfDim_rv_polydisc, VFCategories' finite-map
inequality and VFDimension's arity bound give the one-VF injection bound.
Their actual canonical-model, saturation, small-base and RV-coded-space
hypotheses are discharged. Mathlib ModelTheory.Definability's
Set.definable_iff_finitely_definable supplies a finite internal real support
for both the set and full map graph, rather than a working-code smallness
hypothesis. RawRVSpace0 is the actual RV-coded auxiliary space. The local
539 full-type/axiom audit, root10327-job build and project audits pass.

Partial contractions use the same actual HeadPreparation stages and stop
before complementary VF parameters, with original-Gamma stage graphs and
frozen-coordinate identities proved. No Section4 cell-existence assertion,
external citation or HK theorem enters this batch. Nonzero RV-class
infinitude is proved directly from the checked nontrivial-valuation axiom
using an injective small-power sequence.

## Checked Section4 uniform scalar families (601-head batch)

Merged802eb9c2bed1e0383d52bbcf21acc6b1559771a8, whose full445-head
audit and CI43100323010 passed. Actual GammaRVMap graphs, tagged disjoint
joins, RV attachments, arbitrary-parameter scalar constant/injective families
and finite-image-family refinements are reused through compiled declarations.
Section5 bridges actual mixed tuples to raw uniform families with all frozen
VF parameters and old RV labels free. No unproved cell premise is assumed.
The601 receipt hashes all reused Section4 Lean sources and its verifier.
The62 new full types and actual data definitions were manually reviewed;
full root/project checks pass including Section4.

## Lemma5.6: scalar refinement and actual unary chains

The683-head batch reuses the checked Section4 scalar family theorems to
construct first-tag pieces and separate finite all-constant fibres. The
predecessor's replacementGraphMap/scalar-image bridge and actual GammaIso
operations supply full original-base replacement graphs. Arithmetic swaps
are three actual definable unary bijections; their inverses and point formulas
are proved. Gamma chains are realized as the existing UnaryChain over one
common internal real base, with every factor's original-Gamma graph retained.
The complete finite active-coordinate induction is proved, without importing
a standard-contraction or dimension conclusion. All82 new full types and
actual data constructors were manually reviewed;683-head audit and full
root/project verification pass, with all601 prior complete types unchanged.


## Cell comparison checkpoint,807 audited declarations

The actual Section4 cell geometry at pinned merged source802eb9c supplies
balanced horizontal/vertical fibres, nonemptiness and simultaneous paradigm
degeneracy. No external result is assumed. Matched unary preparations use
this repository's completed5.2 and5.3 with their exact original-base scope.
Pinned Section4 rvIsoOfCarrierEq, rvIsoOfVolumePreservingBijection and
rvReindexVolumeIso reconcile actual key domains and restore volume ordering.
RVUnaryProfiles proves the extra constant-coordinate morphism obligations.
All124 new full types/constructors reviewed;807 allowed-axiom checks,10491-job
root build and full project verifier pass. Product/family compatibility and
the global special-map bridge remain separate obligations.

## Complete cell comparison,912 audited declarations

Actual unary chains lift to either VF coordinate with explicit RV label
suffix compatibility and coverage. Exact product images and computed kernels
supply rectangle comparisons, including singleton factors. Original-Gamma
graph composition certifies the quotient comparison and the matched-tail
profile isomorphism in both directions. Section4 actual cell geometry proves
the cases exhaustive. All105 new complete types/constructors reviewed;912
allowed-axiom checks,10523-job root build and full project audits pass.
The family construction5.8 remains open; pointwise cell comparisons are not
used as an assumed uniform conclusion.

## Mixed cell families and general RV comparison,968 declarations

The twelve family modules generalize the existing repository's Section4
VerticalPositionFamilies, VerticalPresentation, VerticalPullbackCells,
FibreDefinability and PositionRowDefinability proofs to arbitrary old RV
arity. Checked VerticalCharts and ScalarPositionDecomposition already
provide the needed uniform inputs. Applying them to swapped VF input and
recoding by the resulting RV map gives native-order cells with a VF-fixed
actual injection. No new citation or assumed family-uniformity principle.

Pinned special_transformations9cc9760 Section4.LiftBijections contains the
actual injective commuting-lift weight theorem. Its full canonical, valued,
Gamma-space coding, genuine saturation and small-real-base hypotheses are
instantiated in MixedRVIsomorphism; SmallGammaPresentation constructs a small
presentation from finite Gamma support. The general category iso retains
both original-Gamma graphs, while MixedVolumeImages proves finite volume
images from coordinatewise RV-to-VF finiteness. All56 new full types and
constructors reviewed in758 lines;968 audits and full project checks pass.

## Uniform product families and shared positioning,1031 declarations

SharedRVProductProgram generalizes the checked native product construction to
arbitrary common old RV tuples. SharedRVUnaryHeadPreparation uses the exact
image theorem and explicit suffix/coverage compatibility of actual lifted
unary chains; target saturation, program kernels, and both volume coordinates
are proved. The actual Gamma RV2 quotient comparison follows from those
computed kernels and volumes. MixedUnaryPreparations constructs both unary
specials over one common internal base, preserving the originalGamma graphs.

RVKeyedFunctions and PositionedCellLabelInjection transfer the actual selected
vertical positioning function through an injective RV recoding and prove its
agreement with all cell slices. No definable choice of arbitrary cell witnesses
is assumed. RVRectangleCases expresses failure by fourVF coordinates and
projects its actualGamma witness set to the existing RV code. The resulting
finite partition covers the source and its case properties are proved.
NonrectangleCellGeometry reuses the checked cell rectangle/graph/balanced
classification with its explicit nontrivialδ hypothesis. All63 new complete
types/constructors reviewed619lines;1031audits,root10547/fullproject PASS.

## Uniform nonrectangle comparison,1138 declarations

NonrectanglePositionIso constructs one actual originalGamma positioning iso
on the full nonrectangle family using the shared cell-position metadata.
MixedStripPreparation and MixedStripPresentation compute actual canonical/
centripetal first stages, saturation and passive projection isos. MatchedUnaryPreparation
is applied once globally and its square is retained by NonrectangleMatchedHeads.
VariableUnaryProfiles supplies a generic category criterion; its finiteness
premises are discharged by NonrectangleFiniteProfiles using checked
FixedVFFiniteImage, recovered-coordinate Gamma isos and actual transverse
geometry. No VF section of RV or arbitrary definable choice is introduced.
The generic finite combination argument uses finite unions of fixed-VF images;
all arithmetic is applied to finite sets, so no additional definability premise
is needed for those set-theoretic operations. NonrectangleRVComparison transfers
the resulting actual Gamma RV2 iso to both standard contraction objects.
All107 new heads/constructors manually reviewed1495lines;1138 audit and
root10569/fullproject PASS. Finite-branch gluing and5.5 remain open.

## Explicit branch extension and global slice translation,1182 declarations

PartialCoordinateFocus and FocusExtension reuse the existing focus geometry,
intersecting loci with the ambient RV hull and supplying a separate globally
valid head tag. RVPredicateFocus transports arbitrary existing RV-code
predicates through hulls. GammaRVPredicateChain follows the checked unary lift
induction with actual partial foci, including alternation boundaries, suffix
compatibility, coverage and inactive RV-key preservation. No compactness-gluing
conclusion is assumed. RVSliceTranslation constructs a common real presentation
and actual selected-slice and whole-source canonical/focus maps; exact branch
images and Gamma certificates are proved. The global nonrectangle producer
supplies the same actual position for both orders and proves selected-target
head saturation from the checked cell identities. All44 new complete types
and constructors reviewed650lines;1182 audits, root10578 and fullproject PASS.
The finite program/category assembly and5.5 remain open.

## Global branch first heads and head-key descent

Reused the existing RelativeSpecialRestriction.specialRelativeBoundary_restrict,
restrictPointMap and restrictPointImage, preserving actual alternating end kinds.
SharedRVProductImage and unary_product_head_saturated supply the active product
image and saturation. The pinned Map.descend supplies actual definable head-key
descent; a new kernel proof derives bijectivity from fixed VF coordinates,
retained old RV labels and SameRV preservation. Gamma graphs are existential
compositions of the checked full graphs. This1257 batch compiles, all75 new
full types/constructors were reviewed, and root/project/type/axiom checks pass.
These results do not yet establish finite-branch RV-category assembly or5.5.

## Padded unary branch lifts

The1345 batch reuses the actual shared-RV product-image theorem and
specialRelativeBoundary_restrict to prove saturation of the extended active
image. Projection bijectivity follows from its actual source padding iso,
the given local special and the restricted global bijection. SameRV reflection
uses the pinned special inverse-contractibility theorem and explicit coverage
by local-output/retained-old-label coordinates. Head-key padding retains full
Gamma graphs, VF coordinates and old RV indices. All88 new full types and
constructors were reviewed; root10612/fullproject/type/axiom checks pass.
These are explicit proved construction criteria, not the final5.8 assembly.

1561: reused pinned special_transformations9cc9760892092dd34cfad4a6dee655843c52f30c Section4/RVUnionCoproduct.lean: rvUnionDesc constructs both RVHom fields, using finite union of finite volume images; rvUnion_hom_ext and inl/inr laws prove the glued inverse laws. GammaRVUnion adds full original-Gamma union graph certificates over normalized LRV. The pinned source and license are unchanged. All119 additions passed manual type review, full type/allowed-axiom audit, root10655 and project verification.

1686: completed both final branch kernels and volume formulas, Gamma RV partition gluing, whole-program comparison, and Corollary58.lemma_5_8. All125 additions passed full type/constructor review, allowed-axiom audit, root10670 and full project verification; all1561 prior records exact.

Finite category scope (author November12): pinned Section4/RVCategories.lean defines finiteVolumeProperty and RVFiniteObject as the actual full subcategory RV[k]. Pinned Section9/RV-CATEGORY-AUDIT.md and Section10/README.md document the predecessor scope. Reuse the existing ambient comparisons as inputs and ObjectProperty.isoMk to produce actual finite-category isomorphisms after proving both volume maps finite. The checked transfer uses fixed_vf_scalar_image_finite and finite unions of source RV fibres; no dependency or language changes. All finite restatements are included in the1852 full type/axiom audit and full project verification.

Finite-trace bridge (verified in the1852 batch): GammaTraceCore adapts the already
checked scalar-image/affineGraphMap proof of gamma_eta_graph from pinned
special_transformations9cc9760892092dd34cfad4a6dee655843c52f30c Section5/GammaRestriction.lean.
The graph proof does not use global RV-pullback geometry; actual global Focus
geometry is constructed separately in FibreFocusPresentation. The pinned license
and revision remain unchanged. GammaTraceFlags generalizes this project's
GammaMembershipPreparation.gamma_membershipMap_graph from one VF coordinate to
arbitrary finite VF arity and reuses checked Section4 GammaRVMap pair/attachment
operations. The finite compiler and uniform trace retention were developed here;
no unproved external result or new citation is a proof input.

Final RV[k] checkpoint: all166 new complete types and constructor interfaces reviewed in1997 readable lines;1852 full type/allowed-axiom audits, root10708 and full project verification PASS. All1686 earlier complete types and axiom records are exact. The37 new modules supply finite-category restatements and actual global special presentations with explicit VF-fixed Gamma RV charts. No model, parameter-base, code-smallness or preparation conclusion is introduced as an open premise. See STATUS.md for exact scopes.
