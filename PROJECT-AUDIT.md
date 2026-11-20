# Whole-project audit — November 16, 2026

**Update, November 20, 2026 (UTC).** A fresh local check of the
`audit-cleanup` sources passed the root build (13,801 jobs) and the
foundation plus every Section 2–7 verifier. The six registries now contain
**12,877 audited exports**, and every verifier also compares the full
statements of its audited declarations with the committed baseline in
`verification/headline-types/`. All 3,860 section Lean files contain no
admissions or custom axiom declarations outside comments and strings. See
the [current integrity receipt](verification/project-integrity-2026-11-20.json).
CI for these commits is reported separately. The November 16 account below
is historical.

The fresh UTC integrity check passed the root build and foundation plus every
Section 2–7 verifier. The six registries contain **12,597 audited exports**.
All **4,209 published files** at proof commit `862aa448b431` match the cloud
workspace; all **3,720 section Lean files** match that revision and contain
no admissions or custom axiom declarations outside comments and strings.
[Matching CI passed](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43851204054).
The compact [integrity receipt](verification/project-integrity-2026-11-16.json)
retains counts, hashes and identities. The [blueprint](blueprint/README.md)
and [release notes](docs/RELEASE-v1.0.0.md) record the submission package.

The paragraphs below retain the earlier Los Angeles-dated development account;
the current UTC integrity evidence above supersedes earlier publication-pending
language. Source statements and accepted scope boundaries are unchanged.

Dates use America/Los_Angeles. The active Section 7 mathematical targets and
the accepted HK weighted measured-zero correction are complete in their
recorded scope. The upstream pin is `25852c85a31c67069b148bd31348128318303510`.
The sealed Section 7 registry contains 2,041 modules / 6,711 audited exports.
The final 40 modules / 140 exports establish full raw coefficient linearity,
actual supported coordinate and Jacobian maps, and balanced unnormalized
ring-valued Fubini and change of variables in every function degree. Corrected
class 7.10/7.13, normalized 7.14/7.15 and normalized coefficient commutativity
were already checked. See [Section 7 completion](section%207/COMPLETION.md).

The final root build passed 13,548 jobs including valid cached dependencies.
Final automated project verification passed for the foundation and every section; publication and remote CI are reported separately. All standing hypotheses, positive VF dimensions of
the function interfaces, and the accepted nonempty-selected scope of 7.5 are
retained. Other sections' existing documented scope boundaries and approved
corrections are unchanged. The account below retains its historical legacy
interfaces; earlier Section 7 open-boundary paragraphs are superseded by the
completion record.

## Correction and completed integration

Section 5 was already complete in the accepted RV[k] scope on
[`section-5/contracting-to-rv`](https://github.com/daviddhilbert/integration-in-ACVF/tree/73aa1e6c9218bcb01dd67e03cfbe3ec9115ac240).
The earlier audit inspected a stale checkout missing 249 of its modules.
Its conclusions that Section 5 was unfinished and that 5.8 still needed
proof were wrong and are withdrawn.

All 395 published Section 5 Lean sources are now integrated, with hashes
identical to the completed branch. Fresh checks of all 1,852 exported types
and allowed-axiom records pass; all axiom records match the published
receipt. Definition 5.5 retains its documented explicit RV presentation
charts. The imported library and updated root import both build; the final
root integration reports 11,454 Lake jobs, including cached dependencies.

The routine Section 5 verifier now prints readable statement types with
explicit declaration parameters, typed proof-value elisions and all axiom
reports. This took 16 seconds instead of expanding a 572 MB proof-term
report. `--full-proof-terms` retains the historical rendering. Fresh type
hashes use the new format and are not claimed to equal old rendering hashes.
The unchanged expanded receipt remains available at the completed Section 5
commit linked above; its redundant copy was removed from the current tree.
The current receipt is
`section 5/VERIFICATION.json` with its lossless compressed full evidence.

## Current checked mathematical boundary

| Section | Audited exports | Actual boundary |
| --- | ---: | --- |
| 2 | 72 | 2.15 and all-degree 2.34 in their recorded scopes. |
| 3 | 1,244 | Numbered results through 3.24 in the documented scopes and approved corrections. |
| 4 | 445 | Numbered lemmas and cell geometry in the approved scope. |
| 5 | 1,852 | All active RV[k] targets complete, with explicit RV presentation charts for 5.5. |
| 6 | 2,273 + closed API below | 736 original registered modules. The closed generated-base kernel, integration, function and localization interfaces are checked in the new Section 7 batch; their open universal Section 5.8 premise has been removed. |
| 7 | 6,711 in the completion revision | 2,041 checked local modules plus Library. All active corrected targets complete, including full raw semiring/ring function integration and normalized supported 7.14–7.15. See COMPLETION.md for exact scope. |

The three new Section 6 modules convert the actual Section 5 RV-category
isomorphisms and prove `completed_section5_two_order_input` on bases
satisfying 5.8's actual standing hypotheses. Their five complete types and
axiom reports were reviewed, and the affected library build passes.
Evidence is in `section 6/verification/completed-section5/`.
The new closed Section 6 API does not require that universal premise.
It descends the completed Section 5 theorem through definable parameter
closure after every finite VF tuple. Realizing selected RV labels as VF
tails supplies ordinary selected contraction comparisons, retaining zero
RV labels. This gives arbitrary-order independence and the kernel theorem,
then the actual integration, definable-function, Fubini and localization
interfaces. These entrypoints are in
`IntegrationInACVF.Section7.CompletedSection6`; canonical-model and all
standing saturation, field, characteristic and parameter hypotheses remain
visible. The legacy conditional interfaces are preserved.

Section 7 now has actual normalized coefficients: the degree-zero fraction
range in the localization at the central point class, a commutative ring,
and an isomorphism with the raw Grothendieck ring modulo point = cone = 1.
The normalized function space is an actual scalar extension and its total
integral is linear. Prefix-then-total integration agrees on every normalized
function. Positive homogeneous Fubini holds for every coordinate projection.
Head rows equal the actual frozen unary fibre integrals in every homogeneous
degree, including ordinary RV[0]. The positive homogeneous Jacobian transform descends to the supported AE
quotient, is additive and commutes with all coefficient degrees. Its
normalized finite graded assembly is an actual linear operator on the full
normalized function module. Actual restriction splits the supported module
for every definable VF domain, with an injective inclusion, a geometric
support submodule and an idempotent projection. Bijections between arbitrary
definable VF subsets preserve the integral of every source-supported
normalized function, including ordinary RV[0] family generators. These
function modules have positive VF dimension: index n means n+1 VF coordinates.
All standing parameter, saturation and Gamma hypotheses remain explicit.

The actual positive head integral now commutes with every positive constant
coefficient over a VF field base, including the definable closure of each
frozen VF tuple. Actual point padding proves the separately constructed
ordinary-input head map agrees with the normalized operator. Head, prefix
and arbitrary nonempty coordinate pushforwards are linear on the full
normalized module and have the complete graded generator formulas. Their
supported-domain versions have exactly the literal definable projected
support and agree with the unmodified full operators after forgetting
support. Total Fubini holds on every supported normalized input.

Raw Proposition 7.11 is now checked as `proposition_7_11_ring` over the raw Grothendieck ring: its actual signed
coordinate integral preserves literal projected supports and the raw total
for every nonempty coordinate subset. The supported module is proved equal
to the componentwise space of actual supported presentations in every degree,
including ordinary RV[0]. This required no changed coefficient convention.
The published 1,799-module checkpoint at `fbb7d4b0971eeff6e7b16f631f405889baf3753e`
passed CI run43776256489 in9m20s, including every available section verifier.
The latest three local modules passed their fresh type/axiom audit, Library
integration and full root build; their boundary is1,802 modules/5,798 exports.

Section 7 still needs:

- **7.12:** ordinary-input raw Jacobian assembly and its integral identity.
  Positive-supported raw and full normalized change of variables are proved.
- **Assertion preceding 7.13:** the raw, unlocalized single-generator kernel-ideal identification.
  Elementary factorization is proved for source degrees at least two. The
  degree-one source requires an ordinary degree-zero factor that forgets
  density, and that factorization has a checked counterexample. Removing
  degree-zero source objects alone does not address this degree-one relation.
  This does not disprove principal-ideal generation after groupification.

The normalized supported identities are exported as `theorem_7_14` and
`theorem_7_15` in positive VF dimension. The normalized ring presentation is
proved independently of the unresolved raw principal-ideal identification.

The accepted nonempty-selected-coordinate scope of 7.5 is retained;
ordinary RV[0] is included. No new statement relaxation was introduced.

## Publication and verification scope

The durable published checkpoint on `section-7/reconstructed-foundation`
is `ad0b91c9c3a44ed804a56b8a131f4ad5d5656832`, with 1,621 Section 7 modules
and 5,074 exports. [CI run 43761938221](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43761938221)
passed in 8 minutes 20 seconds. The preceding run passed in 9 minutes
31 seconds; compatible compiled-module caching removed the earlier repeated
43-minute project compilation.

The current checked local checkpoint adds 129 modules and 452 exports,
reaching 1,750 modules plus Library and 5,526 exports. Each proof batch
received one complete new-declaration type/axiom review and an affected
Library build. The latest 96-module batch passed 13,030 Lake jobs including
cached dependencies and a complete 6,112-line review of its 361 new exports.
One shared parameter-extension provider was consolidated with its native
Section 5 implementation; its nine exported helper types/axiom reports
received a separate 109-line revalidation. Successful compiler traces cover
every new module. The root now imports `Integration7.Library` and builds.
Publication of this new checkpoint is pending; its CI must be distinguished
from the preceding published run. Main remains
`7d4acc730496b3bd05a22c268ffd89540ca694f9`.

The three CI dispatch regression tests pass. The targeted fresh checks
above supplement the earlier whole-project audit below; its counts and
source hashes describe that older snapshot. They are not presented as a
second all-declaration scan of the new combined source tree.

## Historical whole-project verification

- `lake build` passed, including both default targets, in 12,654 Lake jobs.
  This was a dependency-aware incremental build; valid compiled artifacts
  were reused rather than forcing an unrelated clean recompilation.
- `lake env python3 scripts/verify_ci.py --use-lake-build` passed the eight
  inherited QE headlines and all six section verifiers: **9,072 curated
  type/axiom checks**. Section 6 used 733 Lake-validated modules, with fresh
  type/axiom reports and no excluded drafts.
- The complete fresh audit logs for Sections 2–6 are byte-for-byte identical
  to their earlier checked logs. Section 7 freshly audited all 4,356 entries
  in its current reviewed registry. This is not a claim of a new manual
  line-by-line review of every proof during this run.
- All 2,791 numbered-section Lean files are reachable from their section
  libraries. With the root entry point there are **2,792 Lean source files**;
  every parsed import resolves. Every Section 7 source matches its registry.
- A scan masking nested comments and strings found no executable `sorry`,
  `admit`, custom `axiom`, `unsafe`, `implemented_by` or `extern` markers in
  those 2,792 files.
- All eleven dependency revisions match the manifest, and their tracked
  worktrees are clean. No proof source, toolchain or Lake configuration
  changed during the audit. All three CI dispatch regression tests passed.
- An independent environment scan checked **all 18,437 project declarations**
  in 2,780 modules containing declarations, including generated declarations.
  It found only the permitted axioms and no unsafe declarations. It selects
  declarations by originating module, so declarations placed in inherited
  namespaces are included. Entry points that only reexport imports contribute
  no declarations of their own.

The only permitted axioms in the completed checks are `propext`,
`Classical.choice` and `Quot.sound`. Passing these checks does not discharge
explicit theorem hypotheses or certify every literal printed statement.
In particular, the pinned predecessor does not certify the unrestricted
Gamma clause of its 9.15, reused in the paper's 2.33; the proved 2.34 obtains
its required volume descent independently. The approved language and
statement corrections remain part of the formalization's scope.

## Documentation and evidence

The README's stale claim that Section 7 was a placeholder has been corrected.
The already approved nonempty-selected scope of 7.5 is now also recorded in
`PAPER-CORRECTIONS.md`. Historical receipts for Sections 2–5 retain hashes
of their earlier integration configuration; their section proof sources
are unchanged. Fresh receipts certify the present configuration rather
than rewriting those historical certificates.

Evidence is in `.scratch/project-audit-20261115/`, including `build.log`,
`verification.log`, the per-section receipts, `section-evidence-index.json`,
source and dependency inventories, source snapshots, and the exact local/
remote source comparison. Individual full audit logs are indexed there
under `.scratch/sectionN-verified/HeadlineAudit.log`.

The actual normalized coefficient ring, function scalar extension and linear total integral are now checked; positive homogeneous normalized Jacobian and representative prefix-Fubini identities are included. Full operator assembly and the raw principal-kernel statement remain open.

The normalized coefficient ring now has the exact common-degree homogeneous fraction characterization and an explicit ring equivalence to the raw RV volume ring quotient imposing point=cone=1. Stabilization proves all common-blowup relations after point inversion. This does not discharge the unlocalized single-principal-kernel statement.

Positive homogeneous pointwise head-fibre semantics are now checked in the genuine definable closure of the frozen tuple, using the proved VF field property. Ordinary degree-zero and arbitrary-coordinate full graded assembly remain open.


The raw ideal now has the exact smaller presentation in
`RawBoundaryKernelPresentation.lean`: the basic relation together with all
actual degree-one elementary relations generates the whole kernel. Its
quotient is canonically the VF volume ring. The checked equivalence
`raw_principal_kernel_iff_degree_one` isolates the single-generator question
precisely; it neither assumes nor proves that remaining containment.

The full raw supported function space also has a checked point-padded
change-of-variables identity over the actual Grothendieck coefficient ring:
the transformed integral equals the point coefficient times the original
integral. This retains the raw point factor and is not an unproved
cancellation or a replacement for the still-open ordinary-valued7.12 target.


The numbered Theorem7.13 itself is now checked locally as `theorem_7_13`
and `theorem_7_13_kernel_quotient`. The direct sum of the actual degree
quotients carries the canonical ring structure, retains its original
addition, has its unit in degree zero, and multiplies degrees n,m into
degree n+m. The single-generator assertion preceding that theorem is
separate and remains open. This local three-module addition follows
the published1,799-module checkpoint; its fresh14-export audit and
affected Library build passed.
