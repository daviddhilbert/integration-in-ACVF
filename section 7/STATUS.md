# Section 7 status

Reconstruction is active; the section is not complete. The original working
copy remains unavailable. Lemma 7.5 is restricted to nonempty selected `E`,
as accepted by the author and recorded in `TARGETS.md`.

## Current checked local boundary

`Integration7.Library` integrates 264 source modules plus its entry point.
Full exported types and allowed-axiom reports for 1,046 distinct declarations
have been inspected in targeted incremental batches. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The latest affected-library
build passed, including 10,316 jobs counting its cached dependency closure.
`VERIFICATION.json` seals this source boundary and records the batch receipts.
Unchanged earlier batches were not manually audited again.

The elementary-blowup comparison is established as `elementaryBlowupIso`:
actual elementary blowups of isomorphic positive-degree volume objects are
volume-isomorphic. It uses the concrete admissible charts, the genuine
finite-volume head map, a definable unit correction, and generic existence
of the head and full RV Jacobians. Tangent projection and actual punctured
residue lines identify the determinant; the small head exception gains one
coordinate through the blowup chart. The head-arity-zero case uses the
ordinary empty determinant pointwise. Gamma compatibility holds everywhere
on essential labels and RV compatibility holds outside an RV-small set.
No new Section 5.8 or graph-field hypothesis is present in this theorem.

Other checked material includes volume forms and their operations, actual
volume-isomorphism identity/composition/inversion/relabeling/gluing,
coproducts, graded volume products, iterated-blowup data and Gamma upper-cut
invariants. The independent semiring groupification, central localization
and graded normalization algebra also compile and pass their audits.
Ordinary RV[0], the single absorbing RV element and the reversed valuation
order are retained. Positive selected fibres keep actual finiteness explicit.

Receipts are under `.scratch/recovery/`: the initial algebra and
groupification batches contribute 34 exports; the first geometric batch
contributes 86, the second 59, the third 89, the fourth 26, the fifth 24, the sixth 70, the seventh 56, the eighth 65, the ninth 56, the tenth 23, the eleventh 43, the twelfth 47, the thirteenth 43, the fourteenth 43, the fifteenth 45, the sixteenth 30, the seventeenth 29, and the eighteenth 49.
The latest receipt is `recovered-eighteenth-geometry-receipt.json`.
These checks cover currently available sources, not the historical missing
1,201-module/4,644-declaration working copy.

## Durable remote boundary

Checked reconstruction checkpoints are saved on
`section-7/reconstructed-foundation`. The earlier 62-module/294-export
checkpoint is `3efb1cd01d723fe133c8fab113b2a7f6ae853584`; all 70 file blob
hashes, its ancestry and branch head were verified at publication. Its
project build passed in GitHub Actions run43572697649; section audits were
still running when this newer checkpoint was prepared.

The user has authorized continuing checked GitHub backups without further
permission. The current source boundary is recorded in VERIFICATION.json;
reviewed incremental type/axiom reports and receipts are also preserved in
`verification/reconstruction/`. Exact published revision receipts are kept
locally under `.scratch/recovery/`. Main remains the Section6 revision
`7d4acc730496b3bd05a22c268ffd89540ca694f9`. No pull request has been created.

Sixty recovered original module texts remain unchanged in quarantine under
`.scratch/recovery/transcript/Integration7/`. Canonical promoted copies may
have narrowed imports or split providers. Rebuilt support is distinguished
from recovered originals. Recovery archives include source hashes and audit
logs; see `recovery-delivery/PACKAGING-RECEIPT.json`.

## Common refinement

`volumeBlowup_diamond` constructs one genuine forward blowup on each
branch using four actual definable pieces of the original source.
`IteratedVolumeBlowup.common_refinement_of_iso` proves common refinement
with exact complementary step counts, including isomorphic initial
objects. It uses the independently proved diamond and the existing generic
Section 6 finite-grid argument. `VolumeBlowupEquivalent.trans` and
`muIspSetoid` therefore have no open confluence premise. The ordinary
degree-zero relation remains ordinary RV isomorphism.

The sixth batch also checks the actual source loci, their volume charts,
complement images, essential restrictions, elementary partitions, coproduct
structural isomorphisms, and the additive monoid of volume-isomorphism
classes. All 70 new types and axioms were inspected in its 520-line report.

## VF volume category and lift bridges

The seventh incremental batch proves the exact bridge to the checked
Section 2 density and volume-morphism interfaces, descent of a compatible
volume-preserving lift, and existence of a prescribed volume-preserving
lift of every positive RV volume isomorphism. The original VF/Gamma base
generation hypothesis remains explicit in the existence direction. The
checked Section 2 Gauss-graph construction supplies the predecessor input.

The actual mixed VF volume objects and their lifts are reconstructed.
Full volume-preserving bijections satisfy identity, composition, inversion
and restriction. Almost-everywhere isomorphisms use actual definable
subdomains with VF-small complements; composition uses their middle
intersection and actual preimages/images. Their equivalence relation is
proved. All 56 new exported types and axioms were inspected in a 563-line
report. This is foundation work, not the remaining contraction theorem.

## Density graphs and selected contraction objects

The eighth batch proves the full original-lift comparison by discarding
only the actual smaller-dimensional coordinate-zero locus. It also proves
compatibility of common blowups with addition and constructs their genuine
positive additive quotient and quotient homomorphism. Fresh access to the
paper text confirmed the elementary comparison as Lemma 7.2; the checked
numbered wrapper is `lemma_7_2`. The later batches now establish the complete
all-degree semiring congruence as `lemma_7_4`.

Actual density graphs preserve the VF volume object and the exact selected
fibre finiteness condition. `SelectedVFVolumeFamily` carries a raw same-base
domain, a nonempty selected tuple, its genuine finite fibres and density.
Its rows and ordered augmented contraction objects are constructed. The
latter retain every contracted VF tag and every old selected label. Their
finite-volume property uses the checked Section 6 selected-finiteness
theorem; their density is the retained original density-graph label.
Existence of certified ordered programs retains the standing `VFFieldBase`
assumption. There is no additional Section 5.8 premise.

The 65 new full types and allowed-axiom reports were inspected in 654 lines;
the affected Library build passed with 10,161 jobs including cached imports.
The fibrewise common-blowup comparison of 7.5 is still open. Its construction
objects must not be counted as that comparison theorem.

## Products, signs and uniform density schemata

`RVVolumeIso.prod` proves actual positive products of volume isomorphisms.
Essential product charts are genuine definable bijections. Complementary
normalized tangent projections determine the block determinant; generic
existence supplies full and factor Jacobians. Exceptional products are
bounded by the actual volume degrees, including auxiliary label domains.
Signed coordinate permutations are checked and the recovered
VolumeCoordinatePermutation module is promoted. Ordinary degree-zero factors and multiplicative congruence were treated
separately in the later batches below. Commutativity of the whole volume
ring is not assumed.

The uniform density-schema interface is recovered over the original real/
Gamma base. Function-row validity is proved first-order definable, and valid
rows have unique nonzero densities on exactly their object domain. These
are inputs to the remaining uniform fibrewise comparison, not that theorem.
All56 new full types and axiom reports were inspected in606 lines, and the
affected Library build passed10,173 jobs including cached dependencies.

## Remaining work

Reconstruct the positive selected-family comparison and contraction-order,
lift-kernel, graded integration and function-integration chains. The accepted
nonempty-`E` scope must be witnessed at its consumers. The former architecture
and unavailable providers are recorded in
`.scratch/recovery/HISTORICAL-PROOF-MAP.md`.

## Uniform volume presentations

The tenth batch realizes every valid Gamma RV volume-schema row as a genuine
finite-volume object with a nonzero definable density. The full domain,
coordinate and density graphs retain the original Gamma base plus the actual
parameter row. Only finitely many representative codes are added to an internal
real presentation. Their smallness is proved; generation of that code set is
not asserted. Canonical normalization adapters retain the literal points and
map values. Two presentations of the same graphs give genuine volume
isomorphisms in a containing BaseContext. All 23 new types and axiom reports
were inspected in 343 lines; the affected library passed 10,181 jobs.
This supplies presentation independence, not the remaining uniform witness
cover or the selected-family comparison of Lemma 7.5.

## Positive multiplicative compatibility

The eleventh batch proves actual positive product associativity and right
distributivity, together with the signed product swap. A product chart
constructs an elementary blowup of R times U from an elementary blowup of U.
It retains the actual admissibility, last coordinate and density. The genuine
positive common-blowup relation is now compatible with multiplication on
both sides, including simultaneous replacement of both factors. Right
multiplication uses the determinant sign and common density rescaling;
commutativity of the entire volume ring is not assumed. All 43 new types
and axiom reports were inspected in 586 lines; the affected library passed
10,192 jobs. The later batches below add ordinary RV[0] factors, unit
coherence and the complete graded semiring quotient.

## Ordinary degree-zero factors

The twelfth batch gives actual left and right products with ordinary RV[0]
objects, their coordinate/density identities, genuine volume isomorphisms,
unit isomorphisms and distributivity. Their essential chart retains only the
positive factor's volume coordinates. Its generic Jacobian is compared on
nested correspondences with the positive factor's Jacobian. The exceptional
set is controlled by the zero-dimensional factor's actual finite-volume bound;
no impossible degree-zero almost-everywhere premise is used. Elementary and
common blowups are compatible with these products on both sides. No artificial
point is adjoined or cancelled. All 47 new types and axiom reports were
inspected in 773 lines; the affected library passed 10,201 jobs. The complete
graded multiplication/semiring interface was assembled in the later batches.

The 141-module checkpoint's GitHub Actions run43579893295 was still building
the project when this checkpoint was prepared. This backup commit skips a
duplicate CI dispatch so that running verification can finish. Its result
will cover that exact earlier revision, not the newer 150-module boundary.
The latter has the local source/type/axiom/library checks recorded above.

## All-degree quotient products and coherence

The thirteenth batch proves muIsp_product for the original rvVolumeProduct
in all degrees, including ordinary RV[0]. Actual volume isomorphisms also
have their all-degree product. Both all-degree quotient families are additive
commutative monoids with a well-defined graded product, and their surjective
additive projection preserves that product. Density-bearing product data
proves associativity and both unit isomorphisms for the original product
in every degree. All 43 new exported types, including named instances, were
inspected in 470 lines; the affected library passed 10,210 jobs. Full
distributivity/zero coherence and the graded semiring assembly were completed
in the fourteenth batch. The selected-family comparison of 7.5 remains open.

## Lemma7.4 and graded semiring quotient

The fourteenth batch proves both distributivity laws and both absorbing-zero
laws for the original all-degree product. The left chart is constructed
directly and preserves the original volume-coordinate order. The actual
volume-isomorphism classes and common-blowup classes now form graded
semirings, without a commutativity assumption. The canonical graded
projection is a surjective semiring homomorphism. The numbered lemma_7_4
states equivalence and compatibility with actual coproduct addition and
all-degree multiplication, including ordinary RV[0]. The v2 statement was
compared directly with the source paper. All 43 exported types, including
named instances, were inspected in 519 lines; the affected library passed
10,221 jobs. No part of Lemma7.5 is claimed by this congruence result.

## Uniform finite volume-isomorphism certificates

The fifteenth batch proves parameter extension for actual positive volume
objects, essential isomorphisms, both volume equations, elementary charts
and common forward blowups with exact lengths. Finite VF tuples have genuine
small substructure contexts; neither VF-field closure nor VF/Gamma generation
is asserted for those contexts. Selected rows retain their coordinates and
density.

The native polynomial residue charts have now been parameterized uniformly.
`volumeFamilyChartGraph_definable` proves first-order definability with the
parameter tuple free. `RVVolumeIso.exists_finite_volume_charts` proves a
finite generic cover for every actual volume isomorphism.
`RVVolumeIso.exists_finite_certificate` supplies the actual exceptional set
and a finite-fibre map into fewer RV coordinates; the converse certificate
lemma proves the RV volume equation. No Jacobian existence field or open
geometric obligation was added. The verifier also accepts Lean's explicit
“does not depend on any axioms” report for the finite witness index alias.

All 45 new exported types and reports were inspected in the 609-line audit;
the affected Library build passed 10,235 jobs. The next step remains encoding
and gluing complete common-blowup witnesses over original parameter names.
The accepted positive selected-degree Lemma7.5 remains open.

## Original-Gamma chart formulas and essential rows

The sixteenth batch derives a uniform bound for any actual finite-fibre RV
map over a small real base, using the checked tuple compactness theorem.
Consequently every actual RV volume isomorphism has a finite chart
certificate with a uniformly bounded exceptional map.

The uniform chart graph now descends to the original real/Gamma base.
`gamma_tupleVolumeChartGraph_definable` and its finite-union version do not
add representatives to that base. The general transform lemma explicitly
requires uniform real definability and preservation of sorts; both are
proved for the chart operation in `TupleVolumeChartGraphs`. No open
comparison theorem is used in that application.

Finite-object schemata may be restricted by a definable volume condition
without increasing their bound. `essentialFiniteVolumeSchema` has the exact
nonzero-coordinate domain; `essentialGammaVolumeSchema` retains the actual
density graph and inherits validity. All 30 new exports passed full review
in the 425-line audit and the affected Library build passed 10,243 jobs.
Complete volume-isomorphism and common-blowup witness schemata, their finite
cover and gluing, and the selected-family comparison of7.5 remain open.

The older 141-module CI run43579893295 has completed its project build and
was auditing inherited/project headlines when this checkpoint was prepared.
This is not a CI certificate for the current 192-module sources.

## Finite formula criterion for a fixed essential chart

The seventeenth batch derives the volume correspondence from the actual
source volume graph, comparison chart and target volume graph by relation
inversion and composition over the original Gamma base. Exact row formulas
are proved. The explicit `rvTupleProductTerm` computes the real RV product,
including the empty tuple. `rvProductGammaBalance` is a first-order predicate
for equal Gamma products on nonzero RV tuples; it does not equate RV classes.

The coordinate tuple followed by its density has Gamma product equal to the
actual essential Gamma weight. `rvVolumeIso_finite_formula_iff` gives a
necessary and sufficient criterion for an RV volume isomorphism whose
underlying essential isomorphism is fixed: pointwise product balance and
the actual finite polynomial chart certificate. The smaller-dimensional
exception and its finite map remain explicit in that certificate, with a
uniform bound already proved in the previous batch. This criterion does
not assume the volume isomorphism in its converse direction.

All29 new exported types and reports were inspected in the418-line audit;
the affected Library build passed10,251 jobs. The remaining encoding step
is to package all coordinate/density/chart/exception formulas into complete
first-order isomorphism and common-blowup schemata, prove promotion and
finite-cover/gluing, and apply them to the positive selected7.5 comparison.

## Volume-isomorphism schema validity

The eighteenth batch proves that the actual essential coordinate-and-density
map has finite fibres. Imaging a small exception preserves its dimension
bound, and pulling it back through this map proves the converse. Every
actual RV volume isomorphism therefore supplies finite chart supports and
a bounded exceptional map on the fixed coordinate-and-density label space.
`rvVolumeIsoOfWeightLabelCharts` constructs the actual volume isomorphism
from those charts and the pointwise Gamma equation.

The weighted finite schema retains the original finite bound and exact
coordinate/density values. The density-ratio term uses released RV inversion.
Both pointwise Gamma validity and supported RV-Jacobian validity have
first-order loci over the original real/Gamma base.
`GammaRVVolumeIsoSchema` combines the two volume schemata, essential
comparison chart, finite polynomial supports and an exception schema of
explicitly smaller degree. Its complete validity locus is proved definable.

All49 new exports passed complete639-line type/axiom review and the affected
Library build passed10,261 jobs. Schema realization and promotion of actual
original-Gamma witnesses are not yet proved; neither the common-blowup
witness cover/gluing nor7.5 is claimed. Preserve original-base graph
definability when constructing those witnesses: an arbitrary map in a
containing context with extra representative codes does not supply it.
Internal containing contexts do not acquire VF/Gamma generation.


## Sound realization of volume-isomorphism rows

The nineteenth batch proves exact typed density-ratio and supported chart
semantics, and identifies the derived schema correspondence with the actual
coordinate correspondence of its chart. A valid essential chart constructs
an actual definable bijection. Gamma validity gives pointwise essential
weight balance; RV validity gives the actual polynomial chart values off
the coded exception. Its finite map proves the strict dimension bound.

`GammaRVVolumeIsoSchema.realize` now constructs the source and target volume
presentations, a small containing BaseContext, and an actual RVVolumeIso
realizing the original chart exactly. Only finite internal representative
codes are added. The original real/Gamma chart remains the full graph
certificate; no VF-field or VF/Gamma generation assertion is made about
the containing context. The 10-module/30-export batch passed its full
712-line type/axiom review and the affected 10,271-job Library build.

The converse promotion of genuine original-base volume witnesses into
these schemata is next. Elementary/iterated/common volume-blowup schemata,
the finite witness cover and indexed gluing, and positive selected7.5
remain open. This realization theorem does not discharge those obligations.


## Volume-object promotion and existential exception certificates

Actual original-Gamma volume presentations now promote to valid uniform
coordinate-and-density schemata, with exact raw graph rows and exact
canonical `RVVolumeSchemaRow` interpretations. Density fibres need not be
finite. A globally nonzero guard leaves the given nonzero density row
unchanged; the coordinate map retains its actual finite bound.

`GammaRVVolumeIsoCertificateSchema` permits a finite auxiliary sorted tuple
only in the exceptional set and its finite map. Its validity existentially
quantifies that tuple, and is proved definable over the original real/Gamma
base. Source/target objects, densities, chart and finite polynomial supports
use only the original parameter block. Every valid row realizes an actual
RVVolumeIso with exactly that original chart in a small containing context.
This avoids demanding original-Gamma definability of an arbitrarily chosen
exception map. No definable choice of auxiliary parameters is assumed.

The twentieth 10-module/24-export batch passed full535-line type/axiom
inspection and the affected10,282-job Library build. Complete comparison-
witness promotion is still open: derive the actual finite exceptional-map
encoding over auxiliary parameters, verify the promoted ordinary/Gamma/RV
clauses, then assemble elementary/iterated/common volume-blowup schemata,
finite-cover/gluing and positive selected7.5. No containing context gains
VF-field or VF/Gamma generation merely by adding internal codes.


## Comparison promotion over a named internal context

The twenty-first batch proves the reverse validity implications. An actual
essential bijection gives ordinary row validity; exact weighted fibres and
the actual volume isomorphism give Gamma validity; a finite actual chart
certificate gives supported RV validity. `valid_of_rows` assembles them.

Raw first-order definability over a term-generated substructure descends
to its generators by definable-singleton parameter elimination. Actual
finite exceptional maps therefore promote after naming their finite
auxiliary tuple. `gamma_volume_comparison_promotion` promotes the full
comparison to an existential certificate schema, retaining the exact
original-Gamma chart. `gamma_volume_row_comparison_promotion` also preserves
given source/target schemata exactly.

These promotion theorems explicitly require the internal real context to
be the term closure of the original real base plus the named original and
auxiliary tuples. This is a literal description of that internal context,
not a VF-field or VF/Gamma generation hypothesis. The actual comparison
must carry its full original-Gamma graph; arbitrary real definability over
a containing context is not sufficient. Extending this interface to every
required common-blowup witness still requires the appropriate internal
context construction/transport. No7.5 completion is claimed.

The12-module/23-export batch passed full625-line type/axiom inspection and
the affected10,294-job Library build. Next assemble volume schema row
agreement and actual coproduct/elementary blowup formula operations, then
complete common-blowup witness promotion, finite cover and indexed gluing.


## Density formulas for geometric blowup witnesses

The twenty-second batch supplies full volume-schema row equality and
presentation transport. Coproduct schemata keep the original density on
each tagged summand, with proved exact support, uniqueness and first-order
function validity. Elementary schemata use the native last-coordinate
blowup and pull the density back along the old-label projection. Valid
coordinate-map bounds are obtained from actual finite coproducts and,
for elementary blowups, explicit original-Gamma admissibility.

`GammaRVVolumeBlowupSchema` now has finite center/remainder data and source/
result volume-comparison certificates. Its validity checks full coordinate
and density row equality, admissibility and both comparison certificates;
the complete locus is proved original-base definable. This is formula data
and validity only: realization and promotion of geometric blowup witnesses
are next, followed by chains/common witnesses, finite cover and indexed
gluing. Positive selected7.5 remains open.

The10-module/33-export batch passed full441-line type/axiom review and the
affected10,304-job Library build. The densityTemplate is used only for
native relation-formula operations; it asserts no finite density fibres.
The earlier141-module revision ee03d8d has separately passed GitHub Actions
run43579893295, including the project build and all section verifier steps.
That CI result does not certify this252-module revision.


## Actual blowup witness realization

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
