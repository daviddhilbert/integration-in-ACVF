# Integration in algebraically closed valued fields

Formalization of Yimu Yin's
[Integration in algebraically closed valued fields](https://arxiv.org/abs/0809.0473v2).
This is the sequel to [Special transformations](https://github.com/daviddhilbert/special-transformations),
pinned at `25852c85a31c67069b148bd31348128318303510`. The common ACVF-QE
language, Lean 4.35.0 toolchain and pinned Mathlib revision are unchanged.

| Directory | Paper section |
| --- | --- |
| section 2 | Preliminaries and review |
| section 3 | Parametric balls and atomic subsets |
| section 4 | 2-cells |
| section 5 | Contracting to RV |
| section 6 | The kernel of L without volume forms |
| section 7 | The kernel of L with volume forms and integration |

Section 1 is introductory and has no separate proof target. Section 4 has
checked implementations of all numbered lemmas and its cell geometry.
Section 5 is complete in its accepted RV[k] scope on the published
`section-5/contracting-to-rv` branch; those sources are now integrated locally.
Section 6 now has closed generated-base interfaces for RV[k] and graded
RV[*], deriving the required finite-VF-parameter inputs from the completed
Section 5 theorem. These entrypoints live in
`IntegrationInACVF.Section7.CompletedSection6`. The corrected Section 7 class algebra now includes weighted zero degrees,
its lift/integration equivalence, and the actual single-generator principal
kernel (Theorems 7.10 and 7.13). Weighted-zero AE function integration is
additive and coefficient-linear. The corrected function-level Fubini,
supported change of variables and normalized function assembly remain
unfinished. Earlier ordinary-zero function interfaces retain their legacy
scope. The project is not complete. The checked Section 7 registry contains
1,899 modules plus Library and 6,246 audited exports.
See [Section 5 status](section%205/STATUS.md),
[Section 6 status](section%206/STATUS.md), and
[Section 7 correction status](section%207/HK-CORRECTION-STATUS.md).
Read [WORKFLOW.md](WORKFLOW.md) and [AGENTS.md](AGENTS.md) before proof work.

The author has adopted HK's weighted measured degree zero in this project
and special-transformations. The published upstream API is now consumed;
ordinary RV[0] stays ordinary. Sections 3–6 retain their mathematical scope.
[The impact review](HK-CONVENTION-REVIEW.md) records the required changes.
Ordinary RV[0] and the completed unmeasured Sections 3–6 are retained.

## Checked scope

Section 2 proves Corollary 2.15 over real and genuine Gamma-named bases.
Corollary 2.34 is now proved on the actual finite-volume RV categories in
all degrees. The generic RV equation and the Gamma equation at every
essential label are proved separately. Henselian ascent, finite immediate
triviality, primitive residue lifting and the required degree equality
supply the Gauss graph input. No graph or finite-extension reference
hypothesis remains in the final theorem. Its weighted degree-zero extension retains the supplied label isomorphism
and proves exact preservation of the actual RV form. See [Section 2 status](section%202/STATUS.md).

All 21 numbered Section 3 results through Proposition 3.24 have checked
implementations in their [recorded scopes](section%203/STATUS.md), including
full original real/Gamma/ball parameter bases where stated. The approved
nonemptiness correction in 3.11 and ordinary closed-parent correction in
3.24 are recorded in [PAPER-CORRECTIONS.md](PAPER-CORRECTIONS.md). The open
target in 3.24 still includes VF.

Corollary 3.17's printed conditional exclusion includes VF. Least-radius
existence is additionally constructed on ordinary open source balls.
The identity on VF has no least radius in GammaTop; no author correction
or threshold-function-definability claim is made. This boundary does not
refute the conditional exclusion.

Section 4 proves Lemmas 4.1–4.4 and 4.8, the paradigm slope formulas,
balanced hulls, ball correspondence and internal symmetry, and the unary
cell-decomposition observation. The original Gamma base is retained; 4.8
constructs the finite-arity RV map and proves every cell ingredient definable
over its output labels. The approved “has at most one element” correction
to 4.3 is used. The singleton boundary to the unqualified open-polydisc
observation after 4.7 is independently checked. The author-approved
replacement, “a product of a 1-cell and an open ball,” is proved by
CellRectangles.rectangle.
See [Section 4 status](section%204/STATUS.md).

## Verification

The [whole-project audit](PROJECT-AUDIT.md) records the current checked
boundary, publication state and unfinished mathematical obligations.

The Section 4 integration build and complete project verifiers pass locally
for foundation and Sections 2–5. Section 4 adds 445 full-type/axiom audits;
its source-matched evidence is [VERIFICATION.json](section%204/VERIFICATION.json).
[Section 4 CI 43100323010](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43100323010)
passed, and its retained complete types, axiom records, source/pin hashes
and audit hashes match the local receipt exactly.


The full root build, inherited QE audit, all 68 Section 2 and all 1,244
Section 3 type/axiom audits pass locally. All 54 previous Section 2 types
and all Section 3 types are unchanged; all 14 new complete types match
individual reviewed audits. All 41/368 section source hashes and both audit
hashes match. Only `propext`, `Classical.choice` and `Quot.sound` occur.
The archive is `.scratch/local-closed-volume-68/`, with its own Section2 and
Section3 evidence. [CI 43010073720](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43010073720) passed.
All complete types and source/audit hashes match the reviewed local batch
and publication checkout.

```sh
lake exe cache get
lake build
lake env python3 scripts/verify_ci.py
```

[Lean verification](.github/workflows/lean.yml) runs on pushes, pull requests
and manual dispatch, retaining complete audit evidence. Green CI confirms
the exported types; exact hypotheses and paper fidelity also require manual
review. The section receipts record the checked sources and pins.

The referee attachment remains reference material only; see
[REFERENCE-NOTES.md](REFERENCE-NOTES.md). The requested writeup of proofs
that differ substantially from the paper is deferred until the whole paper
is formalized; its current ledger is [PROOF-WRITEUP.md](PROOF-WRITEUP.md).

Section 6's closed entrypoints include the kernel equivalence, additive
and semiring integration, parameter-dependent definable functions and
linearity, coordinate pushforwards/Fubini, and the principal-ideal and
localization theorem. They retain the standing canonical-model,
saturation, characteristic, field and VF/Gamma-generation hypotheses;
the earlier universal Section 5.8 premise is no longer assumed.
The older conditional interfaces remain available. See
[Section 6 status](section%206/STATUS.md) and
[Section 7 status](section%207/STATUS.md) for their locations and evidence.
The project verifier accepts `--reuse-certified`
to use Section 6's sealed artifact checks while freshly auditing every full
type and permitted-axiom report; default compilation remains fresh.

CI caches the project's compiled modules as well as its pinned predecessors.
The project cache is keyed by the toolchain, dependency manifest, Lake
configuration and commit, with compatible earlier commits used as a fallback.
Lake checks the restored source/import traces and rebuilds affected modules.
Generated `*.setup.json` compiler inputs are excluded from the cache.
CI uses `--use-lake-build` so Section 6 audits these Lake-validated artifacts
instead of compiling the same library a second time in isolation. Every
headline type and axiom report is still checked afresh, and per-section audit
times are retained in `durations.json`. A cold cache still needs a full build.
