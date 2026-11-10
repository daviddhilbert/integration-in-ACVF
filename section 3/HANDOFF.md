# Continue Section 3 here

Read the repository AGENTS.md and WORKFLOW.md, then STATUS.md and
REUSE-SURVEY.md in this folder. The source is arXiv:0809.0473v2, not an old
OpenMathOS working tree. The present session covers Sections 1–3; Section 1
is introductory and Section 2 is principally a reviewed dependency map.

The new entry point is `IntegrationSection3/Library.lean`, registered as
Lake library `IntegrationSection3` with `srcDir = "section 3"`.
It imports Atomicity, BallSupport, DefinableFamilies, ParametricAtomicity
and ImaginaryFamilies, plus the printed-statement checks.
The coordination root additionally imports IntegrationSection3ACVF.Geometry
together with the unchanged pinned Special transformations project.
The core checkpoint passed the library build and 55 declaration type/axiom
checks; `VERIFICATION.json` binds that evidence to the actual source hashes.
The actual ACVF geometry and full real-code ball presentation are written
but awaiting CI compilation; their sixteen headlines are included by the
verifier's --acvf option and the CI driver. BallPresentation now contains
the actual ball-index Lemma 3.2 over real bases, with a definable full graph
and nonalgebraicity of its output-ball imaginary. Full C• bases remain open.

Next mathematical target: finish Lemma 3.2 by connecting `parametric_ball_atomic`
to the actual imaginary ball codes. The finite exceptional index set is now
proved definable over the original base, and its finiteness gives algebraicity.
The generic imaginary interpretation now proves this argument using full
invariant real preimages and no chosen representative named in the base.
It also transfers algebraicity through a definable imaginary function, so
nonalgebraicity can concern the output ball. Verify the actual `Presentation`
and extend the parameter base without naming selected real representatives.
Do not assume atomicity.

Then address Lemma 3.3 (adjoining Gamma parameters), and Lemma 3.4 for open
and closed subballs of a complete-type-generating subset. Retain actual
parameter support throughout. Consult STATUS.md before the later Lemma 3.11
headline because its printed statement needs a nonemptiness qualification.

Run `lake env python3 'section 3/verify.py'` and inspect its complete logs and
headline axiom records. Compiler evidence belongs in
`.scratch/section3-verified/`, and status must distinguish generic components
from the full numbered statements still open.
