# Section 7 continuation

The current checked reconstruction checkpoint is described in `STATUS.md`:
865 source modules plus their library entry point, with 2,706 distinct
exported types and axiom reports inspected. The recovery account below
records the earlier salvage stage; its two-module verification count is
historical, not the current total. Additional reconstruction is continuing
beyond this local checked entry point. Checked checkpoints are backed up on `section-7/reconstructed-foundation`;
the earlier 62-module checkpoint is `3efb1cd01d723fe133c8fab113b2a7f6ae853584`.
The user has authorized continuing checked backup pushes without another
permission request. Published incremental evidence is under
`verification/reconstruction/`.

The accepted target is Lemma 7.5 with a nonempty selected coordinate set.
See [TARGETS.md](TARGETS.md). The empty-set case is excluded from completion
and is not a general blocker for the later applications.

## Workspace recovery boundary

On this continuation the local checkout was the original repository
skeleton at `66d5d19`. The previously reported Section 7 Lean modules,
audit receipts, build artifacts and scratch handoff were absent. No
Section 7 attachment or remote branch was found; the remote default
branch is the pushed Section 6 revision
`7d4acc730496b3bd05a22c268ffd89540ca694f9`.

The committed prerequisites have now been restored from that exact remote
revision: 1,377 Lean files, including the root import, plus their project
configuration and documentation. Existing differing local edits were
preserved; only unchanged skeleton files were updated. The local Git HEAD
was left untouched. Exact byte identities and recovery scope are recorded
in `.scratch/recovery/section6-source-recovery.json`. No fresh Lean build
is claimed for this source recovery.

Sixty Section 7 module sources have since been reconstructed from complete
source reads and creation commands visible in the conversation. They are
quarantined under `.scratch/recovery/transcript/Integration7/`, outside the
project library. Their 314 named declaration heads are a source inventory,
not a newly verified registry. Comments were sometimes shortened, and the
unavailable original receipts prevent a byte-for-byte identity claim.

Two independent algebra modules, `CentralAwayLocalization` and
`GradedUnitNormalization`, have freshly compiled against the pinned Lean
and Mathlib. All 14 exports passed complete type inspection and an axiom
audit allowing only `propext`, `Classical.choice`, and `Quot.sound`; their
importing audit also compiled. The other 58 modules remain unverified
because their dependency closure is incomplete. This is not a Section 7
root build. See `.scratch/recovery/RECOVERY.md` and
`.scratch/recovery/recovered-algebra-receipt.json`.

The session's saved-history reader reports that the earlier work turn
exceeds its read-size limit and cannot be retrieved by that tool. These
observations establish that the proof files are unavailable here; they
do not establish why the earlier working copy is missing or whether it
exists in a platform snapshot elsewhere.

The earlier conversation reported positive-degree results and a registry
of 4,644 declarations in 1,201 Section 7 sources. Those are historical
reports, not verification of this current working copy. No replacement
proofs or axioms have been inserted to stand in for the missing files.

Once the Section 7 working copy is restored, preserve it, update the
positive selected-degree headline and scope documentation, exhibit
nonemptiness at its consumers, and resume the remaining applications.
Do not restart completed proofs or repeat a full audit merely because
this scope restriction was accepted.

The fifteenth reconstruction batch adds uniform certified residue-Jacobian
chart graphs and an actual finite certificate for every RV volume
isomorphism. Complete common-blowup witness schemata, their finite cover
and the selected contraction comparison remain to be proved. Small finite
parameter contexts do not supply field or generation hypotheses.

The sixteenth batch completes original-Gamma descent of the finite chart
formulas and uniform bounds for exceptional maps. Exact essential finite
and density schemata are checked. The next concrete step is encoding the
volume correspondence of a chart and its first-order volume validity, then
promoting and gluing complete common-blowup witnesses.

The seventeenth batch derives original-Gamma volume-correspondence formulas
and proves `rvVolumeIso_finite_formula_iff` for a fixed essential chart.
Its converse constructs the actual RV volume isomorphism from its finite
chart certificate and the explicit Gamma product-balance formula. Next:
assemble complete coordinate/density/chart/exception witness schemata and
their validity/promotion/finite-cover/gluing proofs.7.5 is still open.

The eighteenth batch establishes bounded exceptions on coordinate-and-
density labels, both original-Gamma validity predicates and the finite
`GammaRVVolumeIsoSchema.valid_definable` interface. Its structure has formula
data, not an assumed Jacobian proof. Next prove the semantic coordinate
identities for `weightedJacobianFormula`, realize valid schema rows as
actual volume isomorphisms, and promote genuine original-base witnesses.
Do not infer original-Gamma definability from an arbitrary comparison over
a context containing extra representative codes. Complete common-blowup
schemata, their finite cover/gluing and positive selected7.5 remain open.


The nineteenth batch completes sound realization of every valid original-
Gamma volume-isomorphism schema row. `GammaRVVolumeIsoSchema.realize` gives
actual source/target presentations and an RVVolumeIso in a small containing
context; its full chart is exactly the original schema row. Both volume
clauses and the exception dimension are proved from validity. All 30 new
exports passed the full712-line audit and the affected10,271-job build.
Next promote actual original-base witnesses, then finish volume-blowup
schemata, finite-cover/gluing and selected7.5. The internal extension still
carries no VF-field or VF/Gamma generation claim. Do not repeat older audits.


The twentieth batch promotes actual original-Gamma volume objects and
proves exact canonical row interpretations. Its existential exception
certificate schema has auxiliary parameters only in the exception/map;
all geometry, densities and the comparison chart stay over the original
parameter block. Validity is original-base definable and sound realization
preserves the chart exactly. The24 exports passed full535-line review and
the10,282-job affected build. Next prove comparison-witness promotion:
encode the actual exception map over finitely many auxiliary real names
(eliminate term-closure parameters first), establish ordinary/Gamma/RV
validity from the actual isomorphism, then continue volume-blowup witness
schemata/compactness/gluing. The strict earlier schema remains sound but
must not be assumed to encode an arbitrary original-Gamma exception map.


The twenty-first batch proves complete comparison promotion in an explicitly
named term-generated context (`gamma_volume_comparison_promotion`), with a
fixed-endpoint variant (`gamma_volume_row_comparison_promotion`). Both keep
the full original-Gamma chart hypothesis and literal context equality
explicit. Raw term-closure elimination supplies promotion of the actual
finite exception map. The ordinary/Gamma/RV clauses follow from geometry.
All23 new exports passed625-line review and the10,294-job affected build.
Next implement volume-schema same-row transport, coproduct and elementary
blowup formula/presentation operations, then common witness schemata and
actual promotion/finite-cover/indexed-gluing. Do not treat arbitrary enlarged
real presentations as original-Gamma witnesses or assert field/generation
for internal code contexts. Positive selected7.5 remains open.


The twenty-second batch establishes exact coproduct/elementary density
formulas and function validity, existence of valid coordinate-map bounds,
full schema-row equality/presentation transport, and GammaRVVolumeBlowupSchema
with proved original-base validity. The10 modules/33 exports passed the
full441-line audit and10,304-job affected build. Its geometric realization
and promotion remain open. Next connect actual coproduct/elementary
presentations to these formula rows, realize the splitting certificates
with exact row transport, then build common chains, finite-cover and
indexed gluing. The earlier141-module CI revision ee03d8d passed run43579893295;
the latest source boundary has only the separately recorded local checks.


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
cached dependencies). The checked boundary is 865 source modules plus
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
and the affected Library build (11,565 jobs including cached dependencies).
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
695-line type/axiom review and the affected Library build (11,565 jobs
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
881-line type/axiom review and the affected Library build (11,565 jobs
including cached dependencies). The checked boundary is 564 modules plus
Library, with 1,786 audited exports. This is the next 100-module backup
boundary after the published 464-module checkpoint.


## Published 564-module checkpoint

The checked 564-module/1,786-export boundary is saved on
`section-7/reconstructed-foundation` at commit
`57bc40cdc00e15353027ac4123d174d1d9f8604d`, tree
`5ba8bf3b36dceb740008e84cf1942859cb4784ce`. All 669 uploaded blob
identities, the 464-module parent, branch ref and unchanged main were
verified. GitHub Actions run 43622491340 was pending at publication;
no CI success is claimed. Two local recovery archives were reopened
and byte-verified at the same source boundary.

The next backup is near 664 modules. Continue the actual raw unary
comparison, then the head common-refinement composition and ordered
induction. Lemma 7.5 and later Section 7 targets remain incomplete.


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
891-line type/axiom review and the affected Library build (11,565 jobs
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
459-line type/axiom review and the affected Library build (11,565 jobs
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
346-line type/axiom review and the affected Library build (11,565 jobs
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
316-line type/axiom review and the affected Library build (11,565 jobs
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
review and the affected Library build (11,565 jobs including cached
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
1,832-line type/axiom review and the affected Library build (11,565 jobs
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
1,608-line type/axiom review and the affected Library build (11,565 jobs
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
1,206-line type/axiom review and the affected Library build (11,565 jobs
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

The18-module/85-export batch passed actual source compilation, one full1,702-line type/axiom review and the affected Library build (11,565 jobs including cached dependencies). The checked boundary is696 modules plus Library and2,114 audited exports. The next remote backup remains due around764 modules, following the author’s100-module preference.


## Balanced translation product comparison over the original base

`balanced_translation_product_volume_comparison` constructs actual opposite-order standard contractions of the horizontal and vertical product images of a native balanced cell. Their actual raw RV volume objects are original-Gamma volume-isomorphic, retaining every fixed old RV label and any common nonzero constant density. The real positioning presentation and actual Gamma centre graphs remain explicit; the latter have already been constructed by the checked translation-centre theorem. No contraction-comparison premise is assumed.

The carried-label preparations project by actual Gamma RV isomorphisms to the original compatible unary targets. These projections preserve the unary volume coordinate; adjoining a fixed head or tail coordinate, essential restriction, and the opposite VF order are now all identified. The balance isomorphism from the prepared unary geometry composes with those actual maps in the same real presentation: the smaller RV dimension makes the RV Jacobian clause vacuous, while the pointwise Gamma equation is proved throughout.

`lemma_5_2_gamma_presented_without_field` uses generated VF field names internally and eliminates them from every actual special-chain certificate and the full conjugate graph. The corresponding balanced unary, product and native product frontends therefore require genuine uncountable saturation and smallness of the original real base, without a VFFieldBase hypothesis. Characteristic00, the named value greater than1, actual balanced geometry, nonzero paradigms, their real presentation names and the fixed-label tuple certificates remain explicit.

Lemma7.7 is not yet complete. The remaining bridges include normalized objects and their retained density-graph forms, comparison with arbitrary specified contractions via Corollary7.6, nonbalanced cells, uniform4.8 cell-family assembly and the higher-dimensional frozen-coordinate reduction. Lemma7.5 and Corollary7.6 retain their completed scopes;7.7-7.15 remain unfinished.

The20-module/50-export batch passed actual source compilation, one full1,833-line type/axiom review and the affected Library build (11,565 jobs including cached dependencies). The checked boundary is716 modules plus Library and2,164 audited exports. The durable backup remains the664-module checkpoint46570a319f7bb9a44a53abed2377eca674fefd79. The next remote backup is still due around764 modules under the author’s100-module preference.


## Normalized balanced translation comparison

`balanced_translation_constructed_common_blowup` compares the actual normalized volume objects of the constructed opposite-order standard contractions on the horizontal and vertical translated images of a native balanced cell. The common blowup uses the proved original-Gamma volume isomorphism. The normalized objects are finite, every old RV label retains its source value, and a selected retained nonzero density coordinate gives exactly the constant-density form used in the comparison. Full original-Gamma endpoint and program certificates are proved. No new comparison or field-base premise is assumed.

This does not complete Lemma7.7: comparisons with arbitrary specified original-cell contractions, nonbalanced cells, uniform4.8 cell-family assembly and higher-dimensional exchange remain open. The11-module/39-export batch passed actual compilation, one full935-line type/axiom review and Library integration (11,565 jobs including cached dependencies). The checked boundary is727 modules plus Library and2,203 exports. The next authorized remote backup remains due around764 modules.


## Arbitrary balanced and degenerate cell contractions

`balanced_cell_opposite_order_contraction_comparison` proves the balanced two-dimensional cell case of Lemma7.7 for arbitrary specified original-Gamma standard contractions in the two opposite orders. It constructs actual common forward blowup chains on their normalized finite volume objects, retaining all fixed old RV labels and the selected nonzero density. `gamma_named_balanced_cell_contraction_comparison` realizes the original Gamma names in a genuine small containing context, constructs the actual translation centres and real positioning presentations, and proves the required preservation of original VF independence internally. Nonzero paradigms and their real presentation names remain explicit. No VFFieldBase premise is added.

The key presentation bridge rebuilds actual Gamma special chains over fixed common names while preserving their point values, focus geometry and alternation. The resulting product programs keep their actual target carriers and volume selectors. Their full original-Gamma volume comparison transfers to that presentation, where Corollary7.6 compares the arbitrary specified original-cell contractions to the constructed product contractions. The retained-coordinate density objects are proved equal to the actual normalized constant-density product objects before composition.

`degenerate_cell_contractions_compare` handles zero-paradigm graph cells and singleton-first-projection cells in any specified contraction orders. The actual natural lift maps preserve VF dimension; these domains have VF dimension at most one, so their degree-two contraction objects have empty essential domains. The resulting volume isomorphism and common chains retain the original Gamma base.

The23-module/55-export batch passed actual source compilation, one full1,400-line type/axiom review and Library integration (11,565 jobs including cached dependencies). The checked local boundary is750 modules plus Library and2,258 exports. No earlier batch was manually reviewed again. Complete Lemma7.7 still needs nonbalanced open rectangles, uniform4.8 cell-family assembly and higher-dimensional exchange;7.7-7.15 remain open. The durable backup remains checkpoint664; the next authorized backup is due around764 modules.


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

The13-module/52-export batch passed actual compilation, one complete919-line type/axiom review, and affected Library integration. The checked boundary is865 source modules plus Library, with2,477 exports. The old batches were not manually audited again. The global volume comparison of the whole two-cell family is still open: a fibrewise RV-dimension bound is not asserted for the global family. Full7.7 still needs that comparison and higher-dimensional exchange;7.8-7.15 remain incomplete.


## Specified contraction reduction and uniform vertical geometry

`two_order_cell_family_reduction` reduces two actual specified VF² standard contractions, in any two orders, to actual Gamma-certified contractions of one common definable two-cell family. The two forward volume-blowup comparisons are realized in one genuine containing context. `rv_graph_refinement_contraction_common_blowup` proves the reduction for arbitrary finite-label sources in every positive VF degree, with their literal nonconstant retained density. `gamma_named_two_cell_contraction_reduction` constructs the common-name context and discharges VF-independence preservation internally. `generatedBaseVFField` derives the actual field convention from the already standing generation hypothesis, supplying the checked all-order program producer without a separate field-base assumption.

`UniformMixedCellPresentation` retains the actual global vertical chart, scalar RV refinement and positioning rows behind4.8. The refined centre has an actual native map and complete original-Gamma graph. `refinement_centre_constant` proves its independence from the active VF coordinate when all other VF and refined RV labels are fixed. `source_head_fibre` identifies every complete source head fibre with its actual translated RV class. The corresponding whole-family `verticalTranslation` is bijective onto an original-Gamma head-saturated image, and `vertical_translation_jacobian_one` proves its global AE VF Jacobian equals1. `vertical_translation_standard_contraction_exists` constructs an actual contraction of that image by identity on the complete head fibres followed by unary special preparation over the same common names.

`mixed_translation_contraction_common_blowup` extends the translation comparison to arbitrary carried RV labels in every positive VF degree. Target finiteness follows from the checked Gamma-bijection finiteness theorem; the same literal density coordinate is retained. `rv_cell_family_fibre_contraction_comparison` applies the completed pointwise cell theorem to each actual nonempty labelled fibre, constructing its native pure-VF presentation and all name/tuple certificates.

The17-module/52-export batch passed actual compilation, one complete1,058-line type/axiom review, and affected Library integration. The checked boundary is865 source modules plus Library, with2,529 exports. Earlier batches were not manually audited again. The global opposite-order comparison on a whole cell family remains open: uniform horizontal/product geometry and its full global RV-Jacobian calculation are still needed. Do not promote the pointwise dimension-one calculation to a global RV-dimension bound. Higher-dimensional exchange and7.8-7.15 remain incomplete.


## Uniform balanced horizontal geometry and contraction reductions

The actual mixed positioning map of a balanced-row family is now an original-Gamma bijection retaining every RV label. Its image is exactly the labelled head projection. Inverting that map constructs the actual horizontal centre, whose full graph remains over the original Gamma base and whose value is constant when the other VF coordinate and all RV labels are frozen. Every complete horizontal source fibre is its translated RV class. The whole-family horizontal translation is bijective with VF Jacobian one almost everywhere; after swapping VF coordinates its image is head-saturated and has a constructed opposite-order standard contraction.

`position_compatible_preparation_exists` constructs both compatible unary special preparations and the bijection of prepared RV keys in a genuine small containing context. No finite-unary-label hypothesis is inserted. `vertical_contraction_reduction` and `horizontal_contraction_reduction` connect specified contractions of the actual graph family to constructed contractions of the corresponding translated families by common forward original-Gamma volume blowups. Their density is the same literal original RV coordinate, including nonconstant densities.

The15-module/53-export batch passed actual compilation, one complete1,019-line type/axiom review and affected Library integration. The checked boundary is865 source modules plus Library, with2,582 exports. Earlier batches were not manually audited again. These results complete uniform horizontal geometry in the explicit `BalancedRows` subcase. They do not yet prove the global RV-volume comparison between the two translated families. The full global RV Jacobian, the family case partition, higher-dimensional exchange and7.8-7.15 remain open. The fixed-parameter dimension-one argument is not used as a global dimension bound.


## Actual case partition and selected family geometry

`shape_partition` and `native_shape_partition_cover` construct the actual original-Gamma partition of the cell graph family into zero-paradigm, rectangular, and balanced parts. The rectangle test is the existence of two points in one RV-labelled fibre whose mixed coordinates leave that fibre; four VF witnesses give a direct definable predicate. The paradigm is constant on each retained RV label, and its zero set is obtained from the zero-coordinate locus of the actual uniform translation. These case predicates retain the original Gamma base.

`UniformMixedCellPresentation.select` restricts the actual vertical chart and position rows to whole refinement-parameter fibres. The global centre, paradigm and complete parameter fibres are preserved. `balanced_parameter_selection_rows` proves BalancedRows for the selected balanced part. `balancedNativeRefinement` has exactly the original balanced-part carrier, with all old coordinates and finite-label certificates retained. Both actual translated balanced families have constructed standard contractions in the required opposite orders; no new balanced-case premise is assumed in this selected construction.

`zero_native_part_dimension` bounds the whole zero-paradigm family by VF dimension one, even with varying RV parameters. `zero_native_part_contractions_compare` proves the volume comparison for arbitrary specified orders and arbitrary nonzero retained density. The mixed retained-density lift and dimension lemmas generalize the earlier fixed-label support argument.

For a shared-label rectangle family, a unary special preparation of the actual labelled head projection is extended over a free passive VF coordinate and restricted to the family. Exact old-RV-label preservation and rectangularity make inverse membership constant on head RV fibres, giving a genuine head-saturated target. The full graph remains over the original Gamma base. `rectangle_family_standard_contraction_exists` and its swapped version construct both coordinate orders.

The24-module/124-export batch passed actual compilation, one complete1,872-line type/axiom review and affected Library integration. The checked boundary is865 source modules plus Library, with2,706 exports. Earlier batches were not manually audited again. The global nonzero rectangle and balanced RV-volume comparisons and their assembly remain open, including the full global RV-Jacobian argument for balanced families. Higher-dimensional exchange and7.8-7.15 are incomplete. Do not use the fixed-parameter dimension-one calculation as a global dimension bound.
