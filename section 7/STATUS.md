# Section 7 status

Reconstruction is active; the section is not complete. The original working
copy remains unavailable. Lemma 7.5 is restricted to nonempty selected `E`,
as accepted by the author and recorded in `TARGETS.md`.

## Current checked local boundary

`Integration7.Library` integrates 62 source modules plus its entry point.
Full exported types and allowed-axiom reports for 294 distinct declarations
have been inspected in targeted incremental batches. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. The latest affected-library
build passed, including 9,669 jobs counting its cached dependency closure.
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
contributes 86, the second 59, the third 89, and the fourth 26.
The fourth receipt is `recovered-fourth-geometry-receipt.json`.
These checks cover currently available sources, not the historical missing
1,201-module/4,644-declaration working copy.

## Durable remote boundary

The user-approved first 24-module/120-export checkpoint is saved on
`section-7/reconstructed-foundation` at
`2c6a6945eee43358e676930af3ec3325f56c7f33`. All 32 uploaded blobs were read
back and verified. Main remains the pushed Section 6 revision
`7d4acc730496b3bd05a22c268ffd89540ca694f9`.
Subsequent local proofs are outside that exact upload approval.

Sixty recovered original module texts remain unchanged in quarantine under
`.scratch/recovery/transcript/Integration7/`. Canonical promoted copies may
have narrowed imports or split providers. Rebuilt support is distinguished
from recovered originals. Recovery archives include source hashes and audit
logs; see `recovery-delivery/PACKAGING-RECEIPT.json`.

## Remaining work

Build volume restrictions and overlap refinement, prove common refinement
and transitivity for actual blowups, and reconnect the positive contraction,
lift-kernel, graded integration and function-integration chains. The accepted
nonempty-`E` scope must be witnessed at its consumers. The former architecture
and unavailable providers are recorded in
`.scratch/recovery/HISTORICAL-PROOF-MAP.md`.
