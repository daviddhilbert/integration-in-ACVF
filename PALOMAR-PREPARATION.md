# Selected geometric preparation theorems

The Palomar entry selects two results of Yimu Yin's *Integration in algebraically
closed valued fields*, arXiv:0809.0473v2:

- Proposition 3.19: an actual original-base definable VF bijection admits a
  finite, nonempty-piece, disjoint, definable open-to-open partition.
- Lemma 4.8: an original-Gamma-base definable subset of VF² admits a definable
  map to a finite RV power whose nonempty fibres have definable two-cell data,
  including positioning and paradigms over the original base and output label.

Their complete model, characteristic, saturation, parameter and named-value
hypotheses are retained. See `formalization.yaml` for the exact Lean names.
The rest of the Sections 2–7 library is outside this entry. This follows the
author's standing rule to select a couple of main results, recorded in
AGENTS.md and WORKFLOW.md for reuse by future projects.

The independent Mathlib-only Challenge retains computational definitions and
leaves theorem proofs unspecified. The configuration also compares the helper
proof obligations used in those definitions; they are supporting declarations,
not additional headline paper claims. There are no definition holes. The
Solution imports the two actual proved modules and never imports the Challenge.

Both selected module-format results compiled; their type and axiom output is
retained in `verification/palomar-selected-types.txt`. Only propext,
Classical.choice and Quot.sound occur. The corrected local Comparator diagnostic
passed: statement comparison succeeded and Lean's default kernel accepted the
Solution. This diagnostic ran without the local sandbox and does not replace
Palomar's protected workflow. The Challenge is 94,453 bytes and 990 physical
lines; the compact preparation receipt records its hash and exact scope.

The first intake, at `cfb50be1e464063f3e0368672b79bdc3fba7d0d5`, passed
[Palomar's mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43949736094).
Its later [registration-rendering job](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/43953160407)
failed because 79 compared compiler-generated proof helpers had no source-level
rendering anchor. The corrected configuration selects 37 explicitly named
obligations: the same two headline results and their supporting proof statements.
One tuple-coding surjectivity helper is now an explicit theorem with exactly its
former generated statement; the tuple presentation refers to that theorem.
Computational data, headline types, Solution proofs and dependency pins are
unchanged. No definition holes or additional permitted axioms were introduced.
Both the complete protected mechanical workflow and the trusted rendering
preflight must pass at the corrected commit before a new intake.

The candidate starts from released documentation commit
2c29c5b848f9077274774125222bba563cdc11b4. Module headers and compiler-required
visibility changes are isolated from the released project. The published
Special transformations module adapter is
23157ace335d7c482add99be69d42c07b4ba1d30; ACVF-QE is pinned at
8f90dfd22de9f2c821382830eee326d1f0cf4990. This checks the selected dependency
closure and is not a fresh whole-project audit of the module port.

The Special transformations example at
dd3a4a02aeedcaf322c52186fc25a959145455a6 passed a full preflight for two selected
results; its preparation record explicitly said intake had not been sent.
It is a packaging example, not evidence of this entry's verification.

Palomar's current guidelines and llms.txt were read directly. The pinned full
workflow uses the protected comparison and independent proof checker. A passing
mechanical preflight alone does not certify rendering or registration, so the
branch also checks the pinned trusted renderer before resubmission. Registration
remains a separate decision after the author has seen the actual private review.
