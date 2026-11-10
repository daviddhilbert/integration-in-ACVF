# Continue Section 3 here

Read the repository AGENTS.md and WORKFLOW.md, then STATUS.md and
REUSE-SURVEY.md in this folder. The source is arXiv:0809.0473v2, not an old
OpenMathOS working tree. The present session covers Sections 1–3; Section 1
is introductory. Section 2 records the dependency map and the checked
Corollary 2.15, including genuine Gamma-named bases; Corollary 2.34 is open.

The new entry point is `IntegrationSection3/Library.lean`, registered as
Lake library `IntegrationSection3` with `srcDir = "section 3"`.
It imports Atomicity, BallSupport, DefinableFamilies, ParametricAtomicity
and ImaginaryFamilies, plus the printed-statement checks.
The coordination root additionally imports IntegrationSection3ACVF.Library
together with the unchanged pinned Special transformations project.
The last complete project build and 84 Section 3 audits passed at source
1926587 in CI run 42805178064. `VERIFICATION.json` binds that full audit.
The generic core now has 98 locally passed full type/axiom checks, bound by
`CORE-VERIFICATION.json`. Its additional interpreted-base definitions are in
`ImaginaryParameters.lean` and `ImaginaryBaseFamilies.lean`; they prove
finite-support specialization, Boolean and quantifier closure, the
exceptional-set argument, and algebraicity transfer through definable maps.

Actual ACVF modules: `BallPresentation` proves the real-base Lemma 3.2;
`GammaAtomicity` proves the real-base Lemma 3.3; `BallCosetAtomicity` proves
the actual definable additive-coset instance of Lemma 3.4. Named-RV radii,
definable Gamma radii, singleton balls and VF have compiled in CI. The
combined Gamma/ball `ParameterPresentation` and `FullBaseAtomicity.lemma_3_2`
are undergoing full CI checks. Do not infer completion from their source
being present; inspect the newest build and audit logs. The next bridge is
the precise equivalence between a full family with one additional imaginary
index and definability over the base with that index adjoined.

For Lemma 3.11, the author approved the explicit nonemptiness hypothesis in
`../PAPER-CORRECTIONS.md`. `StatementChecks.complete_type_relation_projections`
proves the resulting projection step; geometric separation is still open.

Run `lake env python3 'section 3/verify.py' --acvf` and inspect its complete logs and
headline axiom records. Compiler evidence belongs in
`.scratch/section3-verified/`, and status must distinguish generic components
from the full numbered statements still open.

Lean 4.35 uses local structure values in instance search even when introduced
with `let`. Freeze original-model sets, carriers and relations before binding
the normalized structure; otherwise a raw definability proof can accidentally
request a second normalization or change the meaning of its input objects.
