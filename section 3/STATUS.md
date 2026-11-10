# Section 3: parametric balls and atomic subsets

Source: arXiv:0809.0473v2, pp. 7–12. The main structural target is the finite
definable partition with the open-to-open property in Proposition 3.19.
The section continues through Proposition 3.24: mixed-coordinate open-to-open
partitions, component/hole counts, and obstructions to geometric bijections
are also in scope. None of those later statements is marked complete.

## Current scope

The full project build and **145 Section 3 declaration type/axiom audits
passed** under Lean 4.35.0 in
[CI run 42812579731](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42812579731),
at source `a8901fd4a9fac6976dc475506706e85ad3ddb35c`.
The audit covers 98 generic declarations and 47 actual ACVF declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur, and the checked
sources have no placeholders or custom axiom declarations. These are
component audits, not 145 numbered paper results.

**Lemma 3.2 is checked with the full additional Gamma/ball parameter base.**
`AdjoinBall.lemma_3_2` concludes atomicity over the original interpreted base
with the input-ball name adjoined. Its nonalgebraicity hypothesis concerns
the output-ball imaginary. All parameter definitions, graphs and tests use
full invariant real-code preimages. No chosen centre or radius
representative is named in the base.

Lemma 3.3 is checked over real bases, with a definable nontrivial Gamma value
explicit. Lemma 3.4 is checked over real bases for every definable ordinary
Gamma radius, for singleton balls and for VF. Extending 3.3 and 3.4 to bases
already containing ball names remains open, as do the later geometric
statements through Proposition 3.24.

`VERIFICATION.json` records the exact compiler, source hashes, dependency pins
and per-headline axioms for the full audit. `CORE-VERIFICATION.json` retains
the corresponding local 98-declaration core audit. Complete logs and both
explicit and compact exported types are in the linked CI artifact and
`.scratch/ci-a8901fd-section3/`. Every recorded input hash was compared with
the committed source revision before publication.

| Component | Source | Scope |
| --- | --- | --- |
| Definition 3.1 and its calculus | `IntegrationSection3/Atomicity.lean` | Actual first-order complete-type generation and atomicity; predicate agreement, parameter restriction, definable subsets and images. |
| Finite Boolean support | `BallSupport.lean` | A finite Boolean combination of a laminar ball family cuts only finitely many members of a disjoint subfamily. |
| Real and imaginary family arguments | `DefinableFamilies.lean`, `ParametricAtomicity.lean`, `ImaginaryFamilies.lean`, `InterpretedRanges.lean` | Same-base definability, finite exceptional sets, algebraicity transfer and atomicity. Geometry is supplied explicitly, not assumed as an atomicity interface. |
| Arbitrary interpreted parameter bases | `ImaginaryParameters.lean`, `ImaginaryBaseFamilies.lean`, `AdjoinParameters.lean` | Finite-support full-preimage definitions, specialization, Boolean/quantifier closure and the family arguments over that exact base. Parameter promotion is proved equivalent to adjoining an imaginary name. |
| Actual ACVF geometry | `IntegrationSection3ACVF/Geometry.lean` | Reuses the pinned predecessor's proved C-minimality and actual valuation-ball geometry. |
| Ball and combined parameter presentations | `BallPresentation.lean`, `ParameterPresentation.lean` | Existing actual ball/Gamma quotients, surjective full real codes, definable membership and interpreted equality. |
| Lemma 3.2 | `FullBaseAtomicity.lean`, `AdjoinBall.lean` | Checked with arbitrary additional real, Gamma and ball names, nonalgebraicity of the output ball, and atomicity over the base plus the input ball. The real-base wrapper remains available in `BallPresentation.lean`. |
| Lemma 3.3 over real bases | `GammaAtomicity.lean` | Every finite actual Gamma tuple preserves atomicity for finite mixed VF/RV tuples; an original-base definable nontrivial value is explicit. |
| Additive-coset instance of Lemma 3.4 | `BallCosetAtomicity.lean` | Actual definable disjoint coset families below a complete-type-generating set, without requiring that ambient set to be definable. |
| Real-base radius cases of Lemma 3.4 | `NamedRadiusAtomicity.lean`, `GammaRadiusAtomicity.lean` | Named nonzero RV radii, ordinary Gamma radii definable over the original base, singleton balls and VF. |
| Corrected Lemma 3.11: logical step | `StatementChecks.lean` | The empty relation is a counterexample to the printed statement. The accepted nonemptiness hypothesis gives surjectivity of both projections between complete types; geometric separation remains open. |
| Later section geometry | Not complete | Primitive types and punctured decompositions, RV-family constancy, open-to-open results, component counts and bijection obstructions remain open. |

The generic core remains independent of ACVF. The concrete presentations
and finite-support parameter calculus interpret the additional names using
the unchanged released LRV structure and its canonical normalization.
The paper's Definition 3.1 does not explicitly require nonemptiness; the code
retains this convention and adds nonemptiness when selecting a realization.

## Current continuation

The Gamma definable-point argument passed all 190 current audits at source
`ca354cd` in CI run 42815859588. Its complete new types, standard axioms and
all receipt input hashes were reviewed. The generic core now has 116 locally
audited declarations, including full-base interpreted ranges and the finite
laminar punctured decomposition. The full-base Lemma 3.3 module compiled in
the subsequent CI run; that run failed in the newly added Lemma 3.4 radius
wrapper, so the new combined checkpoint is not yet certified. Those compiler
issues are being corrected, and the ACVF punctured-decomposition bridge is
compiled in CI. A remaining VF subtraction annotation in the radius proof was corrected for the next run. The finite coset-exception transfer and atomic profile argument are also being checked.
`OpenBallConstancy.lean` now implements Lemma 3.9 and Corollary 3.10 for
ordinary proper open balls, over the full combined base. The proof derives
infinitely many smaller-ball classes from integer translates and the actual
ACVF(0,0) integer-unit theorem, rather than retaining that geometric input.
The two new generic valuation lemmas passed their local full type/axiom audit;
the new ACVF geometry and numbered results await their full CI checks. `VERIFICATION.json` remains the certificate for
the preceding 145-declaration paper-result checkpoint.

## Verification

```sh
lake build IntegrationSection3
lake env python3 'section 3/verify.py'
# Include the actual ACVF declarations:
lake env python3 'section 3/verify.py' --acvf
```

The verifier records exact source/pin/compiler identities, checks all current
headline types and their axiom allowlists, and compiles the library import.
Evidence goes in `.scratch/section3-verified/`. A successful incremental build
does not imply every dependency was freshly compiled in that invocation.
The root `IntegrationInACVF.lean` also imports the predecessor; a check of only
this Section 3 library is not a fresh build of that full coordination root.

## Accepted correction to Lemma 3.11

The printed Lemma 3.11 says a definable relation `A` between two atomic balls
cannot have finite-to-one first projection. Taken literally this includes the
empty relation, whose projection is finite-to-one. Its proof uses both
projections being surjective, which requires `A` to be nonempty. The author
approved adding `A ≠ ∅` on November 10, 2026; see
[`PAPER-CORRECTIONS.md`](../PAPER-CORRECTIONS.md). `StatementChecks.lean` verifies
the empty relation's definability, product containment and finite fibres.
The corrected geometric theorem remains open. This does not affect
Definition 3.1 or the earlier family arguments.
