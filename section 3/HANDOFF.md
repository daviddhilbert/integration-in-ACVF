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
76 Section 3 audits passed in CI run 42789563292. `VERIFICATION.json` binds
the Section 3 evidence to the exact source hashes. The 55 generic and 21
actual ACVF declarations have only the three permitted standard axioms.
BallPresentation contains
the actual ball-index Lemma 3.2 over real bases, with a definable full graph
and nonalgebraicity of its output-ball imaginary. Full C• bases remain open.
GammaAtomicity additionally proves the real-base Lemma 3.3, using the
predecessor's Gamma tuple definable-point theorem and full invariant code
fibres. Both real-base paper instances have passed their full type/axiom audits.

Next mathematical target: extend the real-base cases of Lemmas 3.2–3.3 to
the full C• base with additional Gamma and ball names. The actual ball
presentation is already checked. Keep full invariant real preimages and
the original base throughout; a chosen centre or RV representative must not
silently become a named parameter. Do not assume atomicity or the missing
interpretation as a model-interface field.

For Lemma 3.4, instantiate `atomic_below_complete_type` with the actual
definable disjoint family of same-radius open or closed balls. The ambient
complete-type-generating set need not be definable. Retain actual
parameter support throughout. Consult STATUS.md before the later Lemma 3.11
headline: the author has approved the explicit nonemptiness hypothesis,
recorded in `../PAPER-CORRECTIONS.md`.

Run `lake env python3 'section 3/verify.py' --acvf` and inspect its complete logs and
headline axiom records. Compiler evidence belongs in
`.scratch/section3-verified/`, and status must distinguish generic components
from the full numbered statements still open.

Lean 4.35 uses local structure values in instance search even when introduced
with `let`. Freeze original-model sets, carriers and relations before binding
the normalized structure; otherwise a raw definability proof can accidentally
request a second normalization or change the meaning of its input objects.
