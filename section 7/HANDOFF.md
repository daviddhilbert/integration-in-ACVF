# Section 7 continuation

The current checked reconstruction checkpoint is described in `STATUS.md`:
364 source modules plus their library entry point, with 1,331 distinct
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
