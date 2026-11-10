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
The full local project build, inherited QE audit, Section 2 audit and 551
Section 3 type/axiom audits pass (276 generic, 275 actual ACVF declarations).
The exact hypotheses and evidence are recorded in the section status. The batch also passed
[CI](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42900083681); all551 complete CI types
match the reviewed local audit exactly.

Checked Section 3 results are 3.2, 3.3, 3.4 at original-base definable radii
plus singleton/VF cases, 3.6, 3.7, 3.8, 3.9 and 3.10. The new primitive
classification gives disjoint pieces of the same primitive type, and the image
of a one-component atomic set again has one primitive component. Full real,
Gamma and ball parameter bases are retained. ACVF(0,0) and an original-base
definable nontrivial Gamma value remain explicit where used.

Geometric separation 3.11 and the later results through 3.24 remain open;
3.20 is a definition. Section 2's 2.15 is checked and 2.34 remains open. Keep
the author-approved nonemptiness correction to 3.11 in
[PAPER-CORRECTIONS.md](PAPER-CORRECTIONS.md).
The remaining section folders are placeholders.

For the targeted library and full headline audit:

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
# Also compile and audit the actual ACVF ball presentation:
lake env python3 'section 3/verify.py' --acvf
lake env python3 'section 2/verify.py'
```
