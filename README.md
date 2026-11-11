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
The full local root build, inherited QE audit, Section2 audit and969
Section3 type/axiom audits pass:336 generic and633 actual heads.
All270 source hashes match. All943 previously published complete types
are unchanged; all26 new complete types exactly match individually reviewed
audits. Only propext,Classical.choice andQuot.sound occur. Evidence is in
.scratch/local-full-partition-969/ andVERIFICATION.json. New CI confirmation
is pending. The previous943-head source b11acf2 passed
[CI42964125581](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42964125581)
and was promoted to main at receipt66859e7 after exact type/hash comparison.

FullCompleteTypeOpenImages.lemma_3_15 proves3.15 over the full original
real/Gamma/ball base, for arbitrary open-ball radii inside a possibly
undefinable complete-type set. FullOpenToOpenPartition.proposition_3_19
constructs an actual finite disjoint original-base definable open-to-open
partition of any actual definable VF bijection. Genuine saturation,
infinite cardinal,small original real base,ACVF00 and an original-base
definable nontrivial Gamma value remain explicit. Neither theorem assumes
finiteness or a cardinal bound on the originally named imaginary parameters.

The two remaining numbered Section3 main targets are3.21 and3.24;
3.20 is a definition. Remaining scope followups are unnamed closed-ball
radii in3.4 and existence of the least-radius function supplied as input
in3.17. Section2.34 remains open separately; Section2.15 is checked.

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
