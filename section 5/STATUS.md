# Section 5 status

**Lemmas5.1–5.2, Remark5.3, Definition5.4, Lemma5.6 and all of Lemma5.7 are locally checked.**
The whole section remains in progress: uniform5.8 and the global actual
SpecialBijection bridge of5.5 remain open.

All1257 complete headline types and axiom audits pass, using only propext,
Classical.choice and Quot.sound. All1182 previously published full types and
axiom records are unchanged. All75 new full types and complete constructors
were reviewed in909 readable lines without omissions. The root build
completed10595 jobs. Project audits pass for foundation and Sections2,3,4,5;
Sections6,7 have no verifiers and are skipped. Preserved evidence:
`.scratch/section5-1257-verified/`.

VERIFICATION.json is now a compact index with source/pin identities, all
axiom records, per-type hashes and full-receipt identities. VERIFICATION.json.gz
retains the complete unmodified receipt, including every full type, losslessly.
Decompress it with `gzip -dc 'section 5/VERIFICATION.json.gz'`. The retention
helper checks source/audit hashes, exact source inventory and byte-for-byte
compression round-trip. Raw local and CI audit receipts keep the same format.

The807 checkpoint526f674 passed CI43118540581 and an exact retained artifact
comparison of all807 types/axioms, source hashes, pins and audit logs.
The user explicitly approved the683 checkpoint fast-forward; remote main
is confirmed at30071aff732eac857da238c91e11f76d59f498b4.

## Checked numbered results

Lemma5.1 prepares arbitrary mixed finite maps with actual special bijections,
RV-pullback targets and a contractible conjugate. The set-level wrapper
constructs its common real presentation internally. It uses ACVF00, genuine
saturation, small P.real and VFFieldBase P.real; no internal-code smallness
or target preparation premise is introduced.

Lemma5.2 constructs both specials for an arbitrary unary definable bijection,
mutual contractibility and the unique commuting definable RV-key bijection.
Its original-base scope is ACVF00, genuine saturation with aleph0≤κ, small
P.real, VFFieldBase P.real and a named Gamma value δ with1<δ. The complete
original map graph is explicit. Checked Proposition3.21, finite membership
preparation, actual inverse-special geometry and compatible focus chains
supply the proof. Entry points: UnaryBijection.lemma_5_2 and its presented
wrapper in UnaryBijectionPreparation.

Remark5.3 constructs an actual pinned RV[1,·] isomorphism with both morphism
fields, inverse laws, the induced-key square and full original-Gamma graphs.
Given the actual prepared mutually contractible bijection, it needs only
ACVF, genuine saturation, aleph0≤κ and small P.real. The finite-image and
singleton/nonzero-cell replacement is recorded in PROOF-WRITEUP.md.
Entry point: lemma_5_3 in UnaryRVCategory.

Definition5.4 has actual coordinate-fibre maps and fibrewise special witnesses.
Only complementary VF coordinates enlarge the fibre's real base. Restricted
foci intersect their own fibre RV hull. Descending one-coordinate canonical
factors reproduce the full canonical map, including its labels. Every actual
special bijection factors into actual relatively special factors, in all
arities. The original-Gamma fibre, map and focus graphs are retained.
Entry point: special_relativeSpecial_factorization.

Lemma5.6 now constructs a finite disjoint covering original-Gamma partition
and actual relatively unary definable bijections whose compositions equal
the given map on each piece. One common internal real base presents every
piece and every factor. GammaUnaryChainDefinable certifies every actual
factor over the original Gamma base; the enlarged code set is not a new
smallness hypothesis. Entry points: lemma_5_6 and lemma_5_6_iso in UnaryPartition.
The scope is ACVF00, genuine saturation with aleph0≤κ, small G.real, a named
δ with1<δ and **positive VF arity p+1**. No VFFieldBase hypothesis is needed.
Pure RV arity0 is excluded explicitly: RelativelyUnary requires a VF index.

The5.6 proof uses checked uniform scalar constant/injective refinements.
When all output VF coordinates are constant on a source-head/code fibre,
the inverse scalar's finite image at fixed target VF tuple makes that fibre
finite. Constructed RV labels separate it. First nonconstant tags give a
finite definable partition. Actual coding and coordinate replacement, plus
three arithmetic unary steps for a VF swap, fix one more target coordinate.
Strong induction on the finite active-coordinate set supplies the result,
with frozen VF coordinates and RV labels left free throughout. This replaces
the paper's contraction/dimension proof; see PROOF-WRITEUP.md.

## Standard contraction progress and remaining targets

Uniform relative preparation is constructed from saturation, finite root
means and strict root reduction. Actual unary fibre specials retain legal
alternation and full original-Gamma graphs. gamma_head_preparation restricts
this to arbitrary sources. Certified ordered programs construct a standard
contraction sequence for every coordinate permutation. Its natural map is
bijective onto the actual pinned lift, with explicit volume-coordinate
selector and commuting square. The coordinate-injectivity observation after5.5
is proved. No preparation conclusion or working-code smallness is assumed.

First-n volume normalization is an actual pinned RV-category isomorphism.
The normalized natural lift is bijective, satisfies the square and has full
original-Gamma certificates. The additional **global actual SpecialBijection
bridge remains open**; full5.5 is not yet counted complete. Uniform partial
contractions with frozen VF parameters, exact active RV-pullback geometry,
finite-head RV encoding and the unary-injection RV-weight bound remain
checked support.

The checked Section4 library at802eb9c is merged, including full uniform4.8,
actual cell positioning graphs and balanced geometry. The683 verifier hashes
all reused Section4 Lean sources and its verifier. The singleton first-cell
boundary of the ancillary open-polydisc observation is recorded by Section4;
its valid product conclusion suffices for the5.7 product case.

Next: the uniform4.8 family assembly for5.8 and the explicit global special
presentation bridge for5.5. Neither is claimed from an assumed compatibility
or preparation conclusion.

## Publication evidence

The601-head checkpoint39ec6be passed CI43106272819. Retained artifact13896050077
has SHA25616e8d01f54639803fa37c62074f228944f54a9a2bbe8b2271c21bdead2a03086.
Every receipt field except timestamp, all601 complete types, all source and
dependency hashes, and the retained audit-source/log hashes match the local
receipt. The539-head checkpoint also has an exact retained comparison.
Main advanced separately to36deb895 with Section4 verification documentation;
that documentation-only delta is merged into the current proof checkpoint.
The683 checkpoint passed CI43111040742 and exact retained artifact13896733651
comparison. The807 checkpoint passed CI43118540581 and exact retained
artifact13900877027 comparison. The912 proof checkpoint awaits its own CI.

No HK theorem, referee assertion or new external citation is a proof input.
The paper's precise5.5–5.8 statements and standing conventions were rechecked
against arXiv:0809.0473v2 during this batch.

## Complete Lemma5.7

GammaCellStandardExistence.lemma_5_7_gamma and lemma_5_7_gamma_cell_data
construct both actual StandardContractions and an actual GammaRVIso for
every actual Section4 DefinableTwoCell. Scope: ACVF00, genuine saturation,
aleph0≤κ, small G.real, VFFieldBase G.real and namedδ>1. The common internal
real presentation is constructed and its size is not an extra hypothesis.
Both full programs and both directions of the RV[2] comparison have full
original-Gamma graph certificates.

Balanced cells use matched unary tails after actual strip translations;
injective zero-paradigm graphs use their actual positioning bijection.
Rectangles, including singleton factors, lift actual unary specials and
compare the two programs by their computed equal joint kernels and volume
coordinates. Actual cell geometry proves these cases exhaustive. The final
theorem assumes no case classification or contraction compatibility premise.
The uniform RV-labelled family statement5.8 remains separate.

## Uniform family construction for5.8

CellLabelInjection.exists_cell_label_injection constructs an actual
original-Gamma definable bijection onto its image, fixing the entire VF
coordinate tuple, for every source in VF²×RV^m. Every nonempty native-order
RV slice of the image is an actual definable2-cell over its output RV tuple
and the original base. The mixed vertical presentation, scalar row refinement
and RV recoding are constructed; no uniform cell-existence premise is assumed.
Scope: ACVF00, genuine saturation, aleph0≤κ, small G.real,
VFGammaGeneratedBase G, and namedδ>1. This establishes the cell-label injection
needed for5.8; its uniform contraction comparison remains open.

MixedRVIsomorphism.mixedGammaRVIso constructs an actual RV[n] isomorphism
from an actual mutually contractible definable bijection of RV-pullbacks,
for arbitrary VF arity n. Full original-Gamma graphs of the sets and map,
genuine saturation, aleph0≤κ and small G.real suffice. Internal small real
presentations are constructed from finite Gamma support. The pinned checked
injective commuting-lift dimension theorem proves weight, and fixed-VF
coordinatewise finiteness proves finite-volume images. The input bijection
and contractibility are explicit inputs here; this support theorem is not
counted as the missing uniform5.8 comparison construction.

## Checked uniform rectangle families and positioning metadata

GammaRectangleFamilyComparison.gamma_rectangle_family_comparison constructs
both actual standard contractions and a GammaRVIso for every original-Gamma
mixed family whose RV fibres are rectangles. Unary preparations are constructed
internally; shared RV coordinates, all retained tags, full program graphs,
joint kernels and volume coordinates are computed. Empty and singleton factors
are included. Scope: ACVF00, genuine saturation, small G.real and VFFieldBase
G.real. The rectangle property is the explicit case hypothesis; this is not
claimed as the whole5.8 comparison.

PositionedCellLabelInjection.exists_positioned_cell_label_injection strengthens
the constructed cell-label injection with ONE global original-Gamma positioning
function. Its restrictions agree with the selected positions of every nonempty
native-order cell slice. The source is arbitrary VF²×RV^m in the same scope
as the cell-label injection. RVRectangleCases constructs a finite disjoint
covering original-Gamma partition by RV-code-defined rectangle failure.
Four-VF witnesses detect failure uniformly; the rectangle branch actually has
rectangular fibres and every active nonrectangle slice is proved nonrectangular.
NonrectangleCellGeometry proves that each such cell has balanced or injective
graph positioning, hence a positioning bijection. Uniform nonrectangle comparison is now constructed below. Actual finite-branch
assembly remains open.

The968 checkpointfb486cc passed CI43126821714. Retained artifact13903754659
has SHA256a2c928d96e2af9a2be9e8feb5e2b66f0e8927d301e921c555b533a75c21a016f.
Every receipt field except timestamp, all968 complete types/axioms, all source
hashes and pins, and retained audit-source/log hashes match exactly. The earlier
912 workflow was cancelled by workflow concurrency when968 was pushed; it was
superseded by this passing checkpoint. The1031 checkpointd5d57f9 passed CI43130190054 and exact retained
artifact13905946620 comparison. Its SHA256 is
1aeb5e929609414174af6e8e5739c2e218525fb94eeb64efe04dffe36d0d88c6;
all1031 full types/axioms, receipt fields except timestamp, source hashes,
pins and retained audit-source/log hashes match exactly.

## Uniform nonrectangle comparison,1138 declarations

NonrectangleRVComparison.nonrectangle_standard_comparison in namespace
PositionedCellLabelInjection constructs both actual standard contractions and
an actual GammaRVIso for the entire nonrectangle branch, with all cell RV codes
free. The global positioning bijection, both canonical/centripetal first-stage
preparations, their head saturation and passive projections are constructed.
Lemma5.2 is applied once globally to the actual unary head-source bijection,
retaining its commuting square and all old labels over one common real base.

The varying first RV volume labels have the same absorbing status under the
matched map. Both finite-volume-image obligations are proved: fixed prepared
VF representatives give finitely many recovered passive values and centres;
the actual positioning iso has finite VF image over the resulting finite set
of transverse inputs. The geometric witnesses use c-u in the forward direction
and the inverse position at y+v in the reverse direction. Both RV2 morphisms
and inverse laws are constructed, then actual domain and volume presentations
transfer them to the two standard contraction objects. No uniform RV comparison,
finite-image conclusion or preparation is assumed in the producer.

Scope: ACVF00, genuine saturation with aleph0≤κ, small G.real, VFFieldBase
G.real and a named Gamma valueδ>1. There is no internal-code smallness premise.
This settles the nonrectangle-family case, not the finite-branch assembly of
Corollary5.8. That assembly and the global-special bridge of5.5 remain open.

## Constructed branch extension and global first stages,1182 declarations

GammaRVPredicateChain.gamma_unary_chain_rvPredicateLift constructs an actual
alternating relative-special chain extension on any RV-code branch. It proves
the active projection square, full originalGamma map/target certificates,
old-label suffix compatibility, label coverage, inactive VF preservation and
inactive SameRV preservation. A globally valid head tag is explicit at each
focus boundary; it is constructed by the canonical steps. PartialCoordinateFocus
and RVPredicateFocus construct the actual focus with its full-RV-invariant locus.
These are embedding and boundary criteria, not a claimed final branch assembly.

RVSliceTranslation.rvSlice_translation_preparation constructs one common real
presentation, an actual canonical/centripetal preparation of the selected
RV-code slice, and its extension to the whole source. Both Gamma graphs, the
legal relative-special boundary, the complete on/off formula and exact active
target image are proved. BranchCanonicalFocus also computes the exact inactive
canonical image. GlobalNonrectangleHeads.global_nonrectangle_head_preparations
constructs the shared position and both whole-source extensions in native and
swapped order; their nonrectangle branch targets are actually head-saturated.
InactiveHeadSaturation proves that a head-saturated branch stays head-saturated
under an inactive unary extension fixing its VF coordinate and preserving RV keys.
The rectangle stages, tail gluing, and final RV-category assembly still remain.

The1138 proof checkpoint9afcf55 passed CI43137005878, job130914649155.
Artifact13908972724 has SHA256
49f17b8dad6020c8849c3dfe4eb4f1a57056b9b8a91002d6744aa1e7ea1577d0.
Every receipt field except timestamp, all1138 full types/axioms, source hashes,
pins and retained audit-source/log hashes match the local receipt exactly.

## Completed global first heads and quotient descent,1257 declarations

GlobalCompletedHeads.global_completed_head_preparations constructs both
whole-source first heads. The actual rectangle unary preparations are built
internally over an extension of the existing real presentation. Canonical
prefixes and empty foci meet the alternating boundaries. Exact product images
prove saturation on the rectangle branch, while inactive VF and SameRV
preservation retain saturation on the nonrectangle branch. No branch
preparation or whole-target saturation is assumed in this producer.

FixedVFHeadDescent constructs an actual Gamma isomorphism on head images
from a VF-fixed, label-retaining, SameRV-preserving surjection. The kernel
identity, definable descent, bijectivity and full Gamma graph are proved.
InactiveBranchHeadIso applies it to the actual branch extension and retains
the quotient square. RVSliceHeadImages proves exact branch images and exact
RV-defined head-image slices. Tail gluing and final RV-category assembly of
5.8, and the global-special bridge of5.5, remain open.

The1182 checkpoint2db92b2 passed CI43142254507, job130931755723.
Artifact13911047289 ZIP SHA256:
aa86e81f7c540ca5b2474ec5eaa9769e247b953db15b02cd495aa883555d2c49.
All receipt fields except timestamp, every full type and axiom record, pins,
source hashes and retained audit-source/log hashes match local evidence exactly.
