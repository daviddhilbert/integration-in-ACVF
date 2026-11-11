# Integration in algebraically closed valued fields

Formalization project for Yimu Yin's
[Integration in algebraically closed valued fields](https://arxiv.org/abs/0809.0473v2).

This is the sequel to
[Special transformations](https://github.com/daviddhilbert/special-transformations),
pinned at `9cc9760892092dd34cfad4a6dee655843c52f30c`.
The project uses the same Lean 4.35.0 toolchain and Mathlib revision.
ACVF-QE is inherited through that dependency.

| Directory | Paper section |
| --- | --- |
| section 2 | Preliminaries and review |
| section 3 | Parametric balls and atomic subsets |
| section 4 | 2-cells |
| section 5 | Contracting to RV |
| section 6 | The kernel of L without volume forms |
| section 7 | The kernel of L with volume forms and integration |

Read [WORKFLOW.md](WORKFLOW.md) and [AGENTS.md](AGENTS.md) before proof work.

```sh
lake exe cache get
lake build
lake env python3 scripts/verify_ci.py
```

[Lean verification](.github/workflows/lean.yml) runs on pushes, pull requests
and manual dispatch, with downloadable build and audit evidence.
The current root imports the predecessor and the new Section 2 and 3 libraries.
[Section 2](section%202/STATUS.md) records the prerequisite map and Corollary 2.15;
[Section 3](section%203/STATUS.md) records the exact formalized scope and open work.
The full local root build, inherited QE audit, Section2 audit and1004
Section3 type/axiom audits pass:348 generic and656 actual heads.
All287 source hashes match; all983 previous complete types are unchanged,
and all21 new complete types exactly match individually reviewed audits.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
.scratch/local-coordinate-setup-1004/ and VERIFICATION.json. [CI42971655123](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42971655123) passed;
all1004 full CI types and287 source hashes match the reviewed local archive. The full3.4 source bc7ad74 passed
[CI42968768615](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42968768615)
and was promoted to main at receipt bbcaa66 after exact type/hash matching.
The receipt itself passed CI42970350599.

CompleteTypeBallAtomicity.lemma_3_4 proves full open/closed ball atomicity,
including arbitrary unnamed radii and possibly undefinable complete types.
FullCompleteTypeOpenImages.lemma_3_15 proves3.15 over the full original
real/Gamma/ball base, for arbitrary open-ball radii inside a possibly
undefinable complete-type set. FullOpenToOpenPartition.proposition_3_19
constructs an actual finite disjoint original-base definable open-to-open
partition of any actual definable VF bijection. Genuine saturation,
infinite cardinal,small original real base,ACVF00 and an original-base
definable nontrivial Gamma value remain explicit. Neither theorem assumes
finiteness or a cardinal bound on the originally named imaginary parameters.

The two remaining numbered Section3 main targets are3.21 and3.24;
3.20 is a definition. Lemma3.4 now includes all unnamed open/closed radii.
Existence of the least-radius function supplied as input in3.17 remains
a scope followup. Section2.34 remains open separately; Section2.15 is checked.

Nineteen numbered Section3 results have checked implementations in the
precise scopes listed in the section status. Keep the author-approved
nonemptiness correction in3.11, recorded in PAPER-CORRECTIONS.md.
The referee attachment is reference material only; see REFERENCE-NOTES.md.
The remaining section folders are placeholders.

For the targeted libraries and full headline audits:

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
lake env python3 'section 3/verify.py' --acvf
lake env python3 'section 2/verify.py'
```
