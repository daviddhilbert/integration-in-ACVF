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
The full local root build, inherited QE audit, Section2 audit and943
Section3 type/axiom audits pass:328 generic and615 actual heads.
All255 source hashes match; all926 previous complete types are unchanged,
and all17 new complete types exactly match individually reviewed audits.
Only propext,Classical.choice andQuot.sound occur. Evidence is in
.scratch/local-open-partition-943/ andVERIFICATION.json. CI confirmation
for this batch is pending. The preceding full3.23 checkpoint1cfc67d passed
[CI42961486168](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42961486168)
and was promoted to main at receipt e50f47e after exact type/hash matching.

Proposition 3.23 is complete in
AtomicPrimitiveDistinction.proposition_3_23 for every ordered pair of
distinct actual primitive shapes: open ball, closed ball and thin annulus.
The original full real/Gamma/ball base, atomic source and target, complete
partial VF graph, ACVF00 and an original-base definable nontrivial Gamma
value remain explicit. No saturation or unrestricted3.15 premise is used.

Checked Section 3 results are 3.2, 3.3, 3.4 at original-base definable radii
plus singleton/VF cases, 3.6, 3.7, 3.8, 3.9, 3.10, corrected 3.11, 3.12,
3.13, 3.14, 3.16, 3.17, 3.18, 3.22 and 3.23. Linearity results retain their stated
saturation/small-base scope. Full real,
Gamma and ball bases are retained where permitted.
Lemma 3.14 keeps its restriction to the one source ball imaginary plus old
Gamma names. ACVF(0,0) and an original-base definable nontrivial Gamma value
remain explicit where used. See the section status for exact statements.

Four Section 3 results remain open: 3.15, 3.19, 3.21 and 3.24; 3.20 is a definition.
The extension of 3.4 and 3.15 with old ball parameters remains open; the
real/Gamma-base case now handles arbitrary open-ball radii.
Section 2's 2.15 is checked and 2.34 remains open. Retain the author-approved
nonemptiness correction to 3.11 in [PAPER-CORRECTIONS.md](PAPER-CORRECTIONS.md).
The remaining section folders are placeholders.

For the targeted library and full headline audit:

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
# Also compile and audit the actual ACVF ball presentation:
lake env python3 'section 3/verify.py' --acvf
lake env python3 'section 2/verify.py'
```

Proposition3.19 is now proved over small real parameter bases in
RealOpenToOpenPartition.proposition_3_19_real_base. The output is an actual
finite disjoint partition of the actual VF source into nonempty subsets,
each definable over the unchanged original base and each having the actual
open-to-open property in both directions. Genuine saturation,small real
base,ACVF00,original-base definable nontrivial Gamma value,and
B.imaginary=empty are explicit. The full interpreted-base extension remains
open,so the full-scope count remains four:3.15,3.19,3.21,3.24.
