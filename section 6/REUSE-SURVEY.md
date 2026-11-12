# Section 6 reuse survey

Surveyed November 11, 2026 (America/Los_Angeles).

## Source and dependency identity

- Target: [arXiv:0809.0473v2](https://arxiv.org/html/0809.0473v2#S6),
  Section 6, including the standing assumptions in Section 2.
- Special transformations: `9cc9760892092dd34cfad4a6dee655843c52f30c`.
  Its Lake metadata declares MIT. Definitions below are imported, not copied.
- ACVF-QE: `939346b0a99899e22a873479364e3cc5d142731c`, MIT (LICENSE).
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`, Apache-2.0.
- Lean: `leanprover/lean4:v4.35.0`, release commit
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`.

All eleven dependency checkouts match the committed manifest, checked by
`python3 scripts/prepare_ci.py`. No dependency source or pin was changed.

Read the predecessor's `LANGUAGE-ERRATA.md`. Named, zero-totalized RV inverse
is part of the corrected language; the kernel is the actual 1 + maximal ideal.
RV has one absorbing element. The trivially valued and nontrivially valued
QE statements are separate. Section 6's intended scope retains the sequel's
pure-characteristic-zero and nontrivial base-value-group assumptions.

## Reused interfaces and bridges

| Source | Declarations / evidence inspected | Decision and remaining bridge |
| --- | --- | --- |
| `Section 3/Parameters.lean`, `RawAlgebraicity.lean`, `AlgebraicFinite.lean`, `SmallFiniteParameters.lean` | `AlgebraicAt`, `AlgebraicAt.mono`, finite definable subsets of algebraic closure, `small_union_range` | Actual model-theoretic algebraicity and ordinary `Saturated M κ`. Draft finiteness proofs display `aleph0 ≤ κ`, `mk S < κ` and the added fixed tuple. |
| `Section 3/ClosureBridge.lean`, `Section 4/RealPresentations.lean`, `RVCoordinates.lean` | `rawRVSpace`, `rvValues`, `rvValues_decode`, `finite_rv_set_of_algebraic` | Keep the real-code presentation and full definable preimages. A future named-Gamma base bridge must use existing `Base.real`; it is not established by these drafts. |
| `Section 4/RVCategories.lean` | Full `RVObject` / `RVHom` definitions: definable domain and label map, weight inequality and finite label images for every original label fibre | Use this category. Neither arbitrary set bijections nor volume-preserving bijections alone implement its general isomorphisms. |
| `Section 4/CodeMaps.lean`, `MapProduct.lean`, `RVProduct.lean` | `Map.ofCodes`, `Map.prodMap`, `rvProductDomain`, `rvUnpack`, packing inverse laws | Elementary blowup uses the existing packed finite RV tuples, not a new object type. Its label operation is built from the named multiplication symbol. |
| `Section 3/RVOperations.lean`, `GammaValueEquiv.lean` | `rvGroup`, `mul_val`, `zero_val`, `absoluteHom`, reversed `valueEquiv_rv_le` | Draft positive factor is `¬ iLe s 1`; the draft order bridge proves its absolute value is `< 1`. Include absorbing zero. No RV linear order is introduced. |
| `Section 4/RVRestrictions.lean`, `RVIsoTools.lean`, `RVCoproduct.lean` | Definable restrictions/complements, `rvIsoOfVolumePreservingBijection`, actual tagged coproduct | Reuse for general blowup loci and gluing. General Lemma 6.3 still requires proof for arbitrary RV isomorphisms. |
| `Section 4/RVScissorPresentation.lean`, `RVIsoClassScissors.lean`, `RVFinitePositiveComparison.lean` | Actual positive quotient, actual isomorphism-class comparison, finite counterpart | Do not introduce a replacement free quotient of arbitrary sets. The Isp relation must first be established on actual objects/classes. |
| `Section 4/RVGradedSemiring.lean`, `RVGradedRing.lean`, `RVGroupCompletion.lean` | Actual graded positive semiring, group completion, imported Grothendieck-ring interface | Reuse for 6.19 and 6.22 after the geometric kernel theorem. Padding/filtration and localization comparison remain Section 6 work. |
| `Section 7/PositiveLift.lean`, `PositiveSurjectivity.lean`, `STATUS.md` | `positiveLift` and `corollary_7_7`, including canonical structure, actual small VF/Gamma-generated base, ACVF00, saturation, valuation compatibility and dimension presentation | Reuse the established lifting homomorphism. Do not mistake the predecessor's Section 5 surjectivity for this sequel's Section 5 contraction results. Status includes repaired surjectivity signatures. |
| `Section 7/AlgebraicResidueRoot.lean`, `EncodedHensel.lean`, Section 7 status | Actual residue-root extraction and generalized Hensel exports | Reuse for the focus-map realization in 6.12; the uniform parameter-preserving realization itself remains unproved here. |
| Mathlib `Logic/Relation.lean` | `Relation.ReflTransGen`, `Relation.Join`, `Relation.EqvGen` | Ordinary reflexive/transitive closure forgets exact lengths. A small independent length-indexed `Iteration.Steps` is used for the m/n bounds in 6.5. `Common` uses only forward finite chains, not `EqvGen`. The generic diamond is an explicit premise, not a claimed RV result. |
| Lean core `Quotient` | `Quotient.lift`, `Quotient.sound`, `Quotient.inductionOn` | Generic set-level inverse argument reuses these operations. Additive/semiring descent is deliberately deferred to the actual inherited quotients. |

## Verification boundary

`IntegrationSection6.Iteration` and `IntegrationSection6.Library` have fresh
source compilation and complete exported theorem-type/axiom audits.
The reductions use no mathematical reference axiom. The diamond, exact kernel
identification and surjectivity are visible conditional premises.

The actual RV modules `AlgebraicFibres` and `ElementaryBlowup` are drafts.
Their first compilation cannot yet reach elaboration because the predecessor's
compiled imports are absent. Do not count them as established results.
The cache download and the source dependency build are distinct from the
successful independent core-module checks.

`lake exe cache get` was attempted with a workspace-writable cache directory.
The configured proxy returns HTTP 403 for `cache.mathlib.org`; delayed retries
also failed. The source fallback command is recorded in STATUS.md. In
particular ACVF-QE's pinned `Proofs/Enc.lean` imports all of Mathlib, so even
a small new RV module requires that full external import closure. No pins
or upstream imports were changed to evade this build boundary.


## Active continuation: actual focus and algebraic quotient interfaces

The checkout now contains published upstream main0055851, including the actual
Section 5 standard-contraction, original-Gamma graph and unary RV-isomorphism
interfaces. No published Section 5 theorem has been replaced with a duplicate
language. Its unfinished numbered inputs remain authorized explicitly.

The focus construction reuses the pinned predecessor's
`Section7.exists_originalPolynomial_for_coordinate` and
`simpleResidueRoot_specializeCoordinates`, followed by checked
`generalized_hensel`. The polynomial coefficient field is the original
`vfDefinableClosureFieldBase B`; generated-base field membership supplies
original B.real coefficients. `PolynomialZero.zeroSet_named_definable`
then supplies original-base definability. The new whole-fibre validity and
first-valid-equation gluing adapt the finite-subcover method in pinned
`LiftingDefinability.exists_originalBase_gluedLift` to unique sections,
which require only one direction of lifting. Source attribution is retained
in module comments; these are imported, checked earlier-paper results,
not new external citations. All actual focus modules are still drafts.

The original-Gamma certificate is retained by constructing a real-base root
selector on its entire validity domain and restricting its full graph to the
Gamma-definable source using `gammaLogicInput`. Temporary Gamma representatives
occur only in the saturation-based finite cover, never in the resulting root
equation. Zero unchanged coordinates are eliminated from algebraicity and the
polynomial section is extended back to the full tuple.

The generic groupification modules import the exact pinned attributed
`Section4.Imported.GrothendieckRing` source (Tau Ceti, source attribution and
license retained in the dependency). The selected verifier freshly compiles
that source and records its hash before checking the new quotient and
localization modules. `GroupifiedCongruence` proves the exact ideal determined
by any positive semiring congruence and its quotient comparison; its singleton
generator theorem is generic, not an assumption that Isp has that generator.
`CompletionLocalization` applies directly to the group completion of a graded
positive semiring, allowing the denominator to be a difference of degree-one
classes. `BasicRelationEmbedding` constructs the resulting embedding for the
single positive relation[a]_1=1+[b]_1. The geometric principal-generator
identification for Isp remains open. All these generic sources have passed
individual compilation; the selected audit covers their full exported types
and permitted axioms.


## Verified build and native focus continuation (November12)

The earlier missing-import limitation above is historical. The pinned Mathlib
source build and external prerequisites passed. The64-module Section 6 verifier
now freshly checks154 full types and permitted axioms, and the root build
including those modules passed10523 jobs. The generic Grothendieck source is
reused from its native pinned Lake artifact, with its source hash recorded;
the verifier no longer creates a partial Section 4 prefix that would shadow
other pinned imports.

The actual normalization bridge reuses CanonicalStructure.normalize_fun and
sort preservation, proving idempotence without a new model premise. The
original point sets and full graphs are transported unchanged. The released
Focus.etaImage_pullback and pullbackLiftMap_bijective already supply the
pullback and canonical-lift maps needed for the6.12 diagram; they must be reused.
The new volume-preserving RV lift keeps VF coordinates fixed and proves both
bijection directions and the quotient coordinate, including absorbing zero.
An admissible6.12 input avoids any bound on the internal presentation code set.

## Finite-category scope (user clarification November12)

Only RV[k] and graded RV[*] are targets. RVFiniteObject and
RVFiniteGradedKPlus are the inherited finite-volume categories and quotients.
Section4.RVFiniteScissors.rvFiniteIsoOfAmbient embeds actual ambient
isomorphisms in the full subcategory. Section7.GammaScissors provides
gammaRVFinitePresentation and gammaPositiveFiniteLift on the original
Gamma base. These are the intended original-Gamma quotient providers;
using arbitrary real code names as original parameters would change the
Isp relation and is not an acceptable replacement.

## Original-Gamma finite scissors and graded structure

The pinned MIT Special transformations declarations in
`Section7.GammaScissors` supply the actual `gammaRVFinitePresentation`,
`gammaVFFinitePresentation`, `GammaRVScissor`, `gammaPositiveFiniteLift` and
its finite-object source/target. `lake build +Section7.GammaScissors` passed
9,426 jobs (`.scratch/section6-scissors-prereq.log`). Companion graphs are
retained literally in the new restrictions/partition/coproduct comparison;
no broader RV presentation is substituted. The quotient lift retains the
pinned canonical-structure and VF/Gamma-generation hypotheses. Its inverse
is not claimed before the actual kernel theorem6.17.

The graded class construction follows the pinned MIT
`Section4.RVHomogeneousProducts` and `RVGradedSemiring` pattern. Its actual
structural maps are replaced by finite original-Gamma maps with complete
graphs: product symmetry/associativity and units use explicit real coordinate
programs; distribution uses the actual tagged coproduct. No internal code
smallness or unproved Section 6 input is introduced. The212 fresh-module,
557-type/axiom audit covers products and geometric compatibility. The
expanded230-module audit covers the later scissor and graded construction.

Invariant tuple parameter promotion reuses `promote_gamma_relation` and its
checked support hull from pinned `Section3.GammaBaseTools`, generalizing the
scalar construction in `GammaFullDescent`. Row-validity sets use complement
and real-coordinate projection. Bounded scalar witnesses use the checked
`RawClosure.Tuple.uniform_finite_rows`, after the original-base common-name
bridge. These are ingredients of6.14; neither validity of full blowup witness
schemata nor their prepared-family gluing is assumed.

## RV-indexed validity and descent

The264-module audit includes explicit finite-slice admissibility and indexed
finite-volume/isomorphism gluing, using only the original Gamma base. Its
729 full exported types and allowed-axiom reports and the10,733-job root
build passed. Fixed finite cardinality validity is proved using actual tuple
blocks and Mathlib's checked finite-cardinality injection criterion.
Existence/uniqueness/universal validity use the pinned Gamma Boolean and
projection operations. No definability of Isp is assumed.

Prepared-family descent reuses checked `flatKey_eq_iff`, the full original-
Gamma inverse-chain graph and `gammaLogicInput` composition. The finite
prepared base uses `finiteRVFibres_of_gammaIso` with the actual VF arity
bound and the checked finite-lift-fibre equivalence. Only B.real is small
in this step; original Gamma-name smallness is used separately for genuine
compactness. The private elementary tuple-code injectivity proof in pinned
MIT `Section5.GammaBaseInputs` is exposed through a separately checked public
bridge and explicit sorted decoding, without accessing private declarations.

## Finite object schemata

The272-module/761-full-declaration audit and10,741-job root build passed.
Actual Gamma RV[k] objects are promoted to schemata using the checked
invariant tuple parameter promotion and uniform finite tuple-row bounds.
The validity locus records total/unique volume outputs, the exact source
locus and the actual bounded finite reverse fibres. Every valid specialized
row reconstructs an actual `GammaRVFiniteObject` through the checked full-
graph presentation factory. No abstract definability-of-Isp input is used.
Native RV weight-fibre definability is proved by induction on tuple length;
weight balance is a finite union of matching weight fibres. Normalized real
formulas are transported using the actual equality of the absorbing zeros.

## Weighted isomorphism and admissibility schemata

The287-module/811-full-declaration audit and10,756-job root build passed.
Weighted chart validity combines the actual full source/target volume and
chart formulas with the checked real weight predicate. Every valid row
realizes an actual finite Gamma RV isomorphism through
`gammaIsoOfFiniteRelation`; the inherited two finite volume-image conditions
are proved, not dropped. Conversely every actual finite Gamma isomorphism
promotes with exact raw source, target, volume and chart rows.

Admissibility is encoded by nonzero active coordinates and a fixed finite
bound on coordinate slices of the volume image. The checked finite-slice
criterion proves actual original-base Gamma algebraicity at every valid
row. Conversely checked algebraicity-to-finite-slices plus genuine tuple
compactness supply the fixed bound for any actual admissible object. Only
original real/Gamma names are bounded; no internal representative code set
is required to be small. These close the individual witness-data validity
steps of6.14, while full blowup/chain assembly remains open.

## Uniform native row constructions

The304-module/874-full-declaration audit and10,773-job root build passed.
Uniform elementary and coproduct formulas are compared with the actual
native constructions at every named VF row. Actual finite graph
presentations retain finite extra code sets; coproducts use their explicit
finite code union. Genuine original-base uniform volume bounds make the
same formulas into valid bounded schemata. No additional citation or
Section 6 uniformity input is used.

## Actual finite common-blowup witnesses

The334-module/985-full-declaration audit and10,803-job root build passed.
Native finite row constructions now cover arbitrary sorted parameter
blocks. A common internal code universe gives simultaneous real chart
presentations while retaining complete original-base Gamma graphs.
No smallness of that universe is used. Full finite blowup, chain and common
witnesses have definable validity, actual native realization, and promotion
of every geometric witness. Exact lengths and every intermediate finite
object are retained. Genuine original-base compactness supplies finite
witness covers and bounds on both chain lengths. This discharges the witness
encoding part of6.14, while indexed gluing and the contraction comparison
remain open. The actual finite witness validity is proved from checked
primitive formulas; definability of Isp is never an input.

## Finite indexed objects and charts

The351-module/1,040-full-declaration audit and10,820-job root build passed.
Actual schema rows assemble over an RV[d] base into RV[d+k], using the
base volume and fibre volume together. Admissibility and weighted chart
isomorphisms glue with complete original-base Gamma graphs. Bound-independent
finite row semantics avoid imposing a common numerical bound on derived
families. The native tagged coproduct/index label equivalence uses checked
`Equiv.sigmaSumDistrib` and the project's native RV tags; its complete Gamma
graph is built from their real formulas. This is still support for6.14,
not a claim that witness gluing or the numbered lemma is finished.

## Uniform finite witness gluing over RV indices

The367-module/1,068-full-declaration audit and10,836-job root build passed.
Actual native coproduct and elementary constructions commute with indexed
assembly by full original-Gamma isomorphisms preserving the volume tuple.
The elementary coordinate becomes d+i after the index volume prefix.
These charts glue uniformly valid blowup witnesses, exact-length forward
chains and common-blowup witnesses over an RV[d] base into actual RV[d+k]
geometry. No finite index-set assumption or common derived cardinality
bound is used. The finite-cover and VF preparation stages remain open.

## Full contraction comparisons and selected-volume exchange

At the542-module boundary,6.14 is proved by induction on the actual ordered
program;6.15 uses the checked unary lift comparison and actual relatively
unary fibre maps. The6.16 input `Section5TwoOrderInput` states only the
particular two-order refinement and RV isomorphism of Corollary5.8
(arXiv0809.0473v2, Section 5, lines731–747 in the HTML source checked during
this session). It contains no common-blowup or arbitrary-contraction
independence premise. This is an explicitly authorized unfinished Section 5
result. Earlier unary-only and first-two-only entries above describe their
historical boundaries.

Selected-volume exchange is proved by restricting actual programs to fixed
old RV labels, comparing their actual volume slices, and applying the
checked RV-indexed common-witness gluing. The source restriction uses the
pinned `unaryspecial_restrict_boundary` construction through the checked
Section 5 restriction interface. First-volume normalization reuses
`toFirstVolume_bijective`, `toFirstVolume_volume`, and
`toFirstVolume_oldLabels`, whose full types were inspected. Complete Gamma
graphs are reconstructed with the existing coordinate formula interfaces.
No outside mathematical citation or new Section 6 input is used. The pinned
revisions and licenses remain those recorded above. The selected audit and
root build passed (1,555 full audits;11,011 root jobs); arbitrary-order
independence and the kernel theorem are still separate obligations.

## Native lifting and actual additive integration (600 modules)

The pinned Special transformations local polynomial lifting proofs were
ported with sorted certificates retained, rather than discarded before
normalization. Sources are attributed in NativePolynomialLifts,
NativeBalancedCorrespondenceLifts and NativeGammaLiftGraphs at revision
9cc9760892092dd34cfad4a6dee655843c52f30c; Lake metadata declares MIT.
The resulting general original-Gamma lifting theorem requires no canonical
presentation. Normalization saturation and original-base finite support
are checked imports. No Section 6 result is assumed.

The actual5.7 finite Gamma surjectivity theorem supplies representatives
of arbitrary mixed-arity VF[k] objects. Simultaneous special preparation
proves binary partition additivity, followed by literal scissor descent
using the checked PositiveAdditiveGrothendieck universal property.
Integration and actual lifting are inverse on generators and therefore on
the monoids. Full types, allowed axioms and source/import/pin identities
passed1,703 checks; root integration passed11,069 jobs. The next reuse
survey concerns the pinned finite label compression and padding maps;
their real-base proofs are checked but original-Gamma bridges remain.

## Finite nonzero assembly (619 modules)

Checked predecessor RVLabelCompression, RVCompression, RVWeightRestriction,
RVPadding, RVFinitePadding and RVPaddingSplit supply globally definable
zero deletion, finite fibres, weight preservation and inverse padding.
The new original-Gamma wrappers retain the whole source and volume graph;
they impose no bound on internal code universes. High/low restrictions
and restriction of actual isomorphisms prove uniqueness of the binary
weight split. Iteration constructs the actual F_k additive equivalences.
The nonzero graded semiring inherits the checked product laws, and its
full-weight predicate is proved equivalent to having no absorbing label.

Actual VF zero-coordinate padding is the pinned rvLiftPaddingMap, with its
full original-Gamma graph reconstructed from the real coordinate program.
Full6.17 proves padding preserves and reflects Isp. Consequently filtered
nonzero congruences are compatible and integration quotient transitions
are injective. The619-module audit passed1,776 full types/axioms and the
root build passed11,088 jobs. The global semiring statement is still open.

## Actual global integration (650 modules)

Global finite VF objects retain actual mixed domains, full original-base
Gamma graphs and finite RV fibres. Arity bounds follow from the checked
identity-map dimension criterion. Products are literal Cartesian products.
Original-Gamma product isomorphisms and product-scissor compatibility give
an actual bilinear operation on the global additive scissor monoid.

Finite assembly, coherent direct-sum embeddings and finite-support bounds
construct the Isp union. The fixed6.18 inverse and zero-coordinate lift
padding prove dimension-bound independence, global scissor descent and
both additive inverse laws. Product lifting and the singleton lift prove
compatibility with the graded RV semiring. Injectivity identifies the union
itself as a semiring congruence; equality with the generated congruence is
proved. The6.19 equivalence retains original addition and literal product,
with a full class formula. No unproved6.x result is a premise. The650-module
audit passed1,920 full checks and the root build passed11,119 jobs.

## Nonzero localization (665 modules)

Different-degree weight-preserving isomorphisms preserve the actual
nonzero resolution. Product/padding comparisons make that resolution a
surjective semiring homomorphism. Resolving the positive basic factor
splits off exactly the degree-zero singleton; the remaining factor is
the positive nonabsorbing locus. Thus the nonzero congruence has precisely
the paper's generating pair. Groupification identifies its ideal with
(j−1). The checked canonical completion quotient and generic graded
normalization give theorem_6_22 and its homogeneous formula. The quotient
also satisfies the additive colimit universal property under multiplication
by j, specified on positive generators of each component group. No new
external mathematical input is used. Audit:665 modules,1,981 full checks;
root build:11,134 jobs.

## Parameter-dependent family independence (705 modules)

Countability of the pinned LRV language and Mathlib's checked formula
encoding bound prove smallness of dcl(B,x). The genuine generated-base
condition and VF field convention are derived for each such base. Thus
the coefficient semirings are the actual varying RV/Isp semirings.
Zero padding and finite-stage injectivity prove that equality of coefficients
in different degrees is exactly an actual lift isomorphism. Complete sorted
graph promotion, definable bijection-validity loci and genuine finite-cover
compactness produce a single original-base Gamma bijection of total spaces.
Explicit mixed-coordinate encoding/decoding returns to the inherited point
language. Literal total family lifts have finite RV fibres and integrate
independently of representatives. No6.x conclusion is assumed.
Audit:705 modules,2,155 full checks; root build:11,174 jobs.


## Completed families, Fubini and linearity (733 modules)

The finite-category integration equivalence is reused over the actual bases
dcl(B,x); `VFParameterCoefficientBases` proves their field, size and genuine
VF/Gamma-generation conditions. No fixed coefficient semiring is substituted
for these varying targets. Literal total family lifts and sorted bijection
compactness supply representative independence across RV degrees.

Checked Section 5 partial contraction programs preserve frozen coordinates.
`RelativeFamilyRepresentations` reorders these programs into a presentation
with every retained parameter first and proves the exact parameter identity.
`VFCoordinateProjections.ofSet` covers arbitrary coordinate subsets.
`CoordinatePushforwards` descends actual fibre integration to the function
quotient and proves6.21 by the total-lift isomorphisms.

Native coproducts, products and zero padding construct representatives of
pointwise addition and scalar multiplication. `RVClassBaseChange` identifies
constant-family evaluation with the canonical coefficient-base homomorphism.
`DefinableFunctionSemimodule` identifies the existing quotient with the
submodule of represented varying coefficient functions; operations therefore
have the actual pointwise meanings proved in `DefinableFunctionOperations`.
`LinearFunctionIntegration` gives the actual integral as a linear map, using
the geometric scissor identity and Cartesian-product comparison of total
lifts. There is no assumed Section 6 closure, linearity or Fubini statement.

The 729-module/2,255-declaration audit and11,198-job root build passed before
the final three modules. All732 modules compile individually, and the final
root build passed11,201 jobs. The final expanded audit passed 2,268 full type/axiom checks (2 fresh
modules, 731 certified-reused), with 11,202 root build jobs. Its receipt is
archived in `.scratch/section6-final-733/`. `IntegrationGradedColimit`
directly specializes the additive colimit universal property to the actual
VF Grothendieck group. The project-wide inherited QE and Sections2–6 audits also pass;
Section 7 has no verifier. The explicit `--reuse-certified` project-runner
option forwards Section 6’s sealed reuse checks while preserving fresh
compilation by default.
All sources and hypotheses are checked at the existing dependency pins and
under their previously recorded MIT/Apache license metadata.
