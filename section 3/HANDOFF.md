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
The full project build, inherited foundation audit, two Section 2 audits and
145 Section 3 audits passed at source a8901fd in CI run 42812579731.
`VERIFICATION.json` binds the full Section 3 audit; `CORE-VERIFICATION.json`
retains the local 98-declaration core audit. All input hashes were matched
against the committed source, and the complete new exported types and their
axioms were reviewed. CI retains explicit and compact type output.

`AdjoinBall.lemma_3_2` proves the full additional Gamma/ball-base instance of
Lemma 3.2. It concludes `AtomicOver (B.adjoin (.inl i)) (underlying (f i))`,
with the original-base definable family/function graph, disjoint output balls
and nonalgebraicity of the output-ball name. The combined base uses the
existing actual Gamma and ball quotients; no real representative is named.
`AdjoinParameters.OverBase.adjoin_iff` and its atomicity consequence establish
the precise parameter-promotion equivalence, and AdjoinBall restricts full
combined-sort tests to the ball chart.

The real-base Lemma 3.3 and the real-base definable-radius cases of Lemma 3.4
are also fully checked. Full bases containing additional ball names remain
the next scope extension for these two lemmas.

Next: extend the Gamma definable-point argument to the combined base. Reuse
pinned Section4/GammaControllerDefinability.lean, GammaOrderControllers.lean,
GammaFiniteDefinablePoints.lean, GammaDefinableClosure.lean and
FiniteOrderSamples.lean. Specializing real codes can prove existence of a
finite order controller; the intrinsic minimal controller must then be
shown definable over the original interpreted base. Retain the standing
nontrivial definable value explicitly. Do not replace this by a definable
point over a base enlarged with chosen representatives.

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
