# Section 5 status

**Lemmas 5.1–5.2, Remark 5.3 and the definition/factorization part of 5.4 are locally checked** in the recorded original
real/Gamma base scope. The full Section5 is still in progress. The current
302-declaration full type/axiom audit passes with only propext,
Classical.choice and Quot.sound. All227 prior complete types are unchanged.
The root build and full project audits pass for foundation and Sections2,3,5;
Sections4,6,7 have no local verifiers and are skipped.

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

Next: uniform coordinate preparation and standard contractions(5.5), general5.6 and
2-cell results5.7–5.8 remain open. An arbitrary RV-valued map is not a
standard contraction; an RV-key bijection alone does not prove5.3.

Local evidence: `.scratch/section5-302-verified/`, complete types and exact
source/pin/audit hashes in VERIFICATION.json, and the relative-special root
and project verification logs. All302 type/axiom audits pass. The root build
completed10286 jobs; project audits pass for foundation and Sections2,3,5.
Sections4,6,7 have no local verifiers in this checkout and are skipped.

Published verified checkpoints: f3bd053(121 heads),2428bd0(161),
9426f7e(197, full5.2),a2dd306(227, Remark5.3). The latter passed
CI43083073855; downloaded artifact13885164055 matches all227 complete
local types and all source/dependency/audit hashes exactly. It is on main.
The302-head definition/factorization batch has passed local integration;
remote CI confirmation remains a separate publication step.

No Section5 result is assumed as a prerequisite of itself. No HK result,
referee assertion or new external citation is a proof input. The5.2 proof
follows the paper's partition-and-matching argument. Remark5.3 uses the
verified replacement argument in PROOF-WRITEUP.md. The5.4 fibre and
canonical-coordinate bookkeeping follows the paper's stated construction.
