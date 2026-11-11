# Integration in algebraically closed valued fields

Formalization of Yimu Yin's
[Integration in algebraically closed valued fields](https://arxiv.org/abs/0809.0473v2).
This is the sequel to [Special transformations](https://github.com/daviddhilbert/special-transformations),
pinned at `9cc9760892092dd34cfad4a6dee655843c52f30c`. The common ACVF-QE
language, Lean 4.35.0 toolchain and pinned Mathlib revision are unchanged.

| Directory | Paper section |
| --- | --- |
| section 2 | Preliminaries and review |
| section 3 | Parametric balls and atomic subsets |
| section 4 | 2-cells |
| section 5 | Contracting to RV |
| section 6 | The kernel of L without volume forms |
| section 7 | The kernel of L with volume forms and integration |

Section 1 is introductory and has no separate proof target. Sections 4–7
remain placeholders. Read [WORKFLOW.md](WORKFLOW.md) and [AGENTS.md](AGENTS.md)
before proof work.

## Checked scope

Section 2 proves Corollary 2.15 over real and genuine Gamma-named bases.
Corollary 2.34 is now proved on the actual finite-volume RV categories in
all degrees. The generic RV equation and the Gamma equation at every
essential label are proved separately. Henselian ascent, finite immediate
triviality, primitive residue lifting and the required degree equality
supply the Gauss graph input. No graph or finite-extension reference
hypothesis remains in the final theorem. Degree zero has no volume data
or equation, exactly as `mRV[0] = RV[0]`. See [Section 2 status](section%202/STATUS.md).

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

## Verification

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
