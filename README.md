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
Corollary 2.15 and 306 Section 3 type/axiom audits passed the full project
build in [CI](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42833098057). Lemmas 3.2–3.3
allow additional genuine Gamma and ball names in their base. Lemma 3.4 is
checked at every original-base definable Gamma radius, including the singleton
and whole-field cases. Lemma 3.9 and Corollary 3.10 are checked for every finite
RV output arity, using the full graph on the stated domain and the sequel's
open-ball convention. The standing definable nontrivial Gamma value and
ACVF(0,0) hypotheses remain explicit where used.

The finite disjoint punctured decomposition and the original-base definable
canonical finite ball support, positive-region family and maximal-hole relation
are checked; the primitive-type
classification of Lemma 3.6, Lemmas 3.7–3.8, geometric Lemma 3.11 and the later
open-to-open results remain open. Corollary 2.34 also remains open. The
accepted nonemptiness correction to Lemma 3.11 is recorded in
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
