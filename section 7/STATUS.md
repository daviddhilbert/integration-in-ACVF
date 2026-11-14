# Section 7 status

Reconstruction is active; the section is not complete. The original working
copy remains unavailable. Lemma 7.5 is restricted to nonempty selected `E`,
as accepted by the author and recorded in `TARGETS.md`.

## Current checked local boundary

`Integration7.Library` integrates 159 source modules plus its entry point.
Full exported types and allowed-axiom reports for 721 distinct declarations
have been inspected in targeted incremental batches. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The latest affected-library
build passed, including 10,210 jobs counting its cached dependency closure.
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
contributes 86, the second 59, the third 89, the fourth 26, the fifth 24, the sixth 70, the seventh 56, the eighth 65, the ninth 56, the tenth 23, the eleventh 43, the twelfth 47, and the thirteenth 43.
The latest receipt is `recovered-thirteenth-geometry-receipt.json`.
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
numbered wrapper is `lemma_7_2`. Graded multiplicative compatibility in 7.4
remains to be established.

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
VolumeCoordinatePermutation module is promoted. Ordinary degree-zero
factors still require their separate arguments; no commutativity of the
whole volume ring or full multiplicative blowup congruence is claimed.

The uniform density-schema interface is recovered over the original real/
Gamma base. Function-row validity is proved first-order definable, and valid
rows have unique nonzero densities on exactly their object domain. These
are inputs to the remaining uniform fibrewise comparison, not that theorem.
All56 new full types and axiom reports were inspected in606 lines, and the
affected Library build passed10,181 jobs including cached dependencies.

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
10,192 jobs. Ordinary RV[0] factors, unit coherence and the complete graded
semiring quotient still require their separate constructions.

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
graded multiplication/semiring interface still needs assembly and coherence.

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
distributivity/zero coherence and the graded semiring assembly are still
separate work. The selected-family comparison of 7.5 remains open.
