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
The full local root build, inherited QE audit, Section2 audit and1100
Section3 type/axiom audits pass:356 generic and744 actual heads.
All318 source hashes match; all1051 previous complete types are unchanged,
and all49 new complete types exactly match individually reviewed audits.
Only propext, Classical.choice and Quot.sound occur. Evidence is in
.scratch/local-radial-matching-1100/ and VERIFICATION.json. CI confirmation
for the radial/RV/Gamma matching batch is pending. The preceding source948714a
passed [CI42975906264](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42975906264)
and was promoted to main with the approved3.24 correction at receiptc8f4270
following exact type/source/audit matching.

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

CoordinatePartitions.proposition_3_21 now supplies full uniform finite
original-base partitions with the open-to-open property on all selected
VF coordinate pairs in actual mixed finite tuple maps.

The literal whole-field boundary of3.24 has a checked nonempty identity
counterexample. The author approved the ordinary closed-parent restriction, recorded in
[PAPER-CORRECTIONS.md](PAPER-CORRECTIONS.md). The corrected obstruction is open.

The only remaining numbered Section3 main target is3.24;
3.20 is a definition. Lemma3.4 now includes all unnamed open/closed radii.
Existence of the least-radius function supplied as input in3.17 remains
a scope followup. Section2.34 remains open separately; Section2.15 is checked.

Twenty numbered Section3 results have checked implementations in the
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
