# Section 5 status

**Lemmas5.1–5.2, Remark5.3, Definition5.4 and Lemma5.6 are locally checked.**
The whole section remains in progress: the global actual SpecialBijection
bridge in5.5 and actual two-cell results5.7–5.8 are still open.

All683 complete headline types and axiom audits pass, using only propext,
Classical.choice and Quot.sound. All601 prior types are unchanged. All82 new
full types, complete data constructors and the recursive original-Gamma
certificate were reviewed in920 readable lines without omissions. The root
build completed10458 jobs. Full project audits pass for foundation and
Sections2,3,4,5; Sections6,7 have no verifiers and are skipped. Preserved
receipt: `.scratch/section5-683-verified/`; hashes and scope: VERIFICATION.json.

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

Next: actual cell translations/product contractions, RV[2,·] isomorphisms
for5.7, then the uniform4.8 family assembly for5.8. Neither5.7 nor5.8 is claimed
from an assumed cell-existence or chosen-contraction compatibility premise.

## Publication evidence

The601-head checkpoint39ec6be passed CI43106272819. Retained artifact13896050077
has SHA25616e8d01f54639803fa37c62074f228944f54a9a2bbe8b2271c21bdead2a03086.
Every receipt field except timestamp, all601 complete types, all source and
dependency hashes, and the retained audit-source/log hashes match the local
receipt. The539-head checkpoint also has an exact retained comparison.
Main advanced separately to36deb895 with Section4 verification documentation;
that documentation-only delta is merged into the current proof checkpoint.
The683 checkpoint still requires its own remote CI and retained comparison.

No HK theorem, referee assertion or new external citation is a proof input.
The paper's precise5.5–5.8 statements and standing conventions were rechecked
against arXiv:0809.0473v2 during this batch.
