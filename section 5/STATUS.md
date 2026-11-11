# Section 5 status

**Lemmas 5.1–5.2, Remark 5.3 and the definition/factorization part of 5.4 are locally checked** in the recorded original
real/Gamma base scope. The full Section5 is still in progress. The current
601-declaration full type/axiom audit passes with only propext,
Classical.choice and Quot.sound. All539 prior complete types are unchanged.
The root build and full project audits pass for foundation and Sections2,3,4,5;
Sections6,7 have no local verifiers and are skipped.

Lemma5.1 prepares arbitrary mixed finite maps. Lemma5.2 now constructs both
special bijections for an arbitrary unary definable bijection and produces
the unique commuting definable RV-key bijection. Its final theorem does
not assume contractibility, inverse contractibility, an open-to-open
partition or the desired geometric equivalence.

The original-base5.2 scope is ACVF(0,0), genuine saturation with aleph0≤κ,
small P.real, VFFieldBase P.real and a named Gamma value δ with1<δ.
The complete original map graph and domain definability are explicit.
Internal real presentations may be enlarged, but every constructed focus
and special chain has a full invariant certificate over the original P.
No smallness bound on the internal code set or ball names is introduced.

The proof imports checked Proposition3.21, proves the Gamma/no-ball-full-base
bridge and its mixed tuple translation, then prepares all finite partition
membership flags. Actual inverse-special geometry yields the required
open-to-open property. Compatible chain induction matches every target
focus, keeping both directions contractible. Boundary alternation and the
existing last canonical step are tracked explicitly. Inverse preparation
comes from genuine saturation and the checked predecessor producer.

Entry points: `UnaryBijection.lemma_5_2` is the set-level result;
`UnaryBijectionPreparation.lemma_5_2_gamma_presented` starts from an actual
working real presentation. `UnaryBijectionFromPartition` and
`GammaOpenPreparation` record the assembly. `GammaFullBaseBridge`,
`GammaPointRawBridge`, `GammaGraphRawBridge` and `UnaryCoordinatePartition`
retain original-base semantics. `GammaMembershipPreparation` prepares
finite map families at an explicit chain boundary. The earlier geometry,
quotient and relatively-unary modules remain checked support.

Remark5.3 now constructs actual RV[1,·] morphisms in both directions,
including weight, finite-volume-image conditions and inverse laws. The maps
retain full invariant original-Gamma graphs and the induced-key square.
The standalone consequence requires only ACVF, genuine saturation with
aleph0≤κ and small P.real, plus the actual mutual contractibility and
RV-pullback data supplied by5.2. No internal code-set smallness is used.
`UnaryRVCategory.lemma_5_3` is the entry point; `unaryRVIso` is the actual
category isomorphism. `UnaryVFFibreFinite` proves fixed-input VF finiteness;
`UnaryVolumeImages` proves the required category finiteness.

Definition5.4 now has actual coordinate-fibre maps and exact fibrewise
special witnesses, rather than just the relatively-unary predicate. The
fibre base names only the complementary VF coordinates; its Gamma names
are unchanged. Restricted focus loci are intersected with the fibre RV
hull. One-coordinate canonical factors, applied in descending coordinate
order, reproduce the full canonical map exactly, including its RV labels.
`special_relativeSpecial_factorization` factors every actual special
bijection into actual relatively special factors, in all finite arities.
The original-Gamma fibre-set, full-map and focus graphs are proved in
`GammaCoordinateFibres`. This batch needs only ACVF and the actual given
maps/foci, with no saturation or smallness premise.

Uniform relative preparation of an ambient original-Gamma relation is now
constructed by `relative_prepare_gamma_relation`. It requires genuine
saturation, ACVF00, small P.real and VFFieldBase P.real, and returns an actual
head preparation over P.real with fibre-special chains and explicit legal
alternation. No Gamma representatives or smallness of a working code set
are introduced. The real-RV producer `relative_prepare_realRV` derives its
finite obstacles from saturation; bounded finite-root means and strict root
reduction construct the maps. Inverse affine and ordinary-ball slice
geometry come from actual unary fibre special witnesses.

`gamma_head_preparation` now restricts uniform ambient preparations to arbitrary
original-Gamma sources, with actual fibre specials and full original-Gamma
map graphs. `gamma_ordered_contraction_program_certified` constructs each
stage recursively. `standard_contraction_exists` constructs the sequence
for every VF-coordinate permutation. Its natural map is bijective onto the
actual pinned RV lift, with the explicit injective volume-coordinate selector
and commuting square. The coordinate-difference/injectivity observation
following5.5 is proved by `original_coordinate_injective_on_final_line`.
No working-code smallness or preparation conclusion is a premise.

The first-n volume convention is now explicit: `normalizationIso` is an
actual volume-preserving isomorphism in the pinned RV category, retaining
all old labels. `normalizedNaturalLiftMap` is bijective onto its actual
pinned lift and satisfies the square. `gammaNormalizedObject` and
`gammaNormalizedLiftIso` retain complete original-Gamma certificates.
The global actual SpecialBijection bridge for this natural map remains
open; full5.5 is not yet counted as complete.

Uniform partial contractions now stop before a frozen VF tuple.
`gamma_partial_contraction_program` constructs their actual stages with
original-Gamma graphs, and `naturalImage_frozen_pullback` proves exact
active-coordinate RV-pullback geometry. The coordinate-difference and
injectivity observations extend to these partial contractions.
`finite_head_family_rv_encoding` constructs separating RV labels for finite
head fibres. `unary_injection_polydisc_weight_le` proves that an RV polydisc
injecting definably into one VF coordinate has weight at most one; finite
formula support supplies an internal small base, so no smallness of the
working code set is assumed. These are support for5.6, whose general
partition-and-factorization theorem remains open. The actual2-cell
results5.7–5.8 also remain open.

Local evidence: all539 full type/axiom audits pass, with all467 prior types
unchanged. The72 new types and actual partial-program/certificate definitions
were manually reviewed in a631-line readable export with proofs and deep
terms enabled, without omissions. The root build completed10327 jobs.
Full project verification passes for foundation and Sections2,3,5, with4,6,7
skipped(no local verifiers). Preserved receipt:
`.scratch/section5-539-verified/`. Exact source, type, dependency and
integration hashes are recorded in VERIFICATION.json.

Published verified checkpoints: f3bd053(121 heads),2428bd0(161),
9426f7e(197, full5.2),a2dd306(227, Remark5.3),53b98da(302, actual5.4
fibre specialness and exact factorization). The latter passed CI43087844851;
downloaded artifact13887054661 matches all302 complete types and every
source/dependency/audit hash exactly. It is on main.

No Section5 result is assumed as a prerequisite of itself. No HK result,
referee assertion or new external citation is a proof input. The5.2 proof
follows the paper's partition-and-matching argument. Remark5.3 uses the
verified replacement argument in PROOF-WRITEUP.md. The uniform relative
preparation expands the checked finite-root argument underlying the paper's
cited preparation theorem; it is not yet classified as a different proof of
a completed numbered target.

## Uniform scalar refinement for 5.6

The checked Section4 cell/family library at802eb9c is now merged. Its full
local and CI checks passed; Section5 retains its source hashes as proof inputs.
Uniform original-Gamma codes simultaneously classify every output VF scalar
as constant or injective on each source-head fibre with frozen complementary
VF coordinates and old RV labels. For an actual bijection, all-constant code
fibres are finite: the inverse head scalar has finite image when its full
input VF tuple is fixed. An actual VF-preserving RV attachment and a constructed
finite-family RV code separate those fibres. These are checked prerequisites,
not the complete partition/factorization theorem5.6. All601 full types/axioms,
the10435-job root build and full project verifier pass. The62 new complete
types and actual data definitions were manually reviewed in552 readable lines.
Preserved evidence: `.scratch/section5-601-verified/`.

The next step combines the singleton all-constant case with tagged injective
branches, constructs a finite definable coordinate partition, then proves
actual relatively-unary coordinate updates and the uniform induction.
The global-special bridge of5.5 and5.7–5.8 remain open.
