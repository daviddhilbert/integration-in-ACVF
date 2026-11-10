# Continue Section 3 here

Read the repository AGENTS.md and WORKFLOW.md, then STATUS.md and
REUSE-SURVEY.md in this folder. The source is arXiv:0809.0473v2, not an old
OpenMathOS working tree. The present session covers Sections 1–3; Section 1
is introductory and Section 2 is principally a reviewed dependency map.

The new entry point is `IntegrationSection3/Library.lean`, registered as
Lake library `IntegrationSection3` with `srcDir = "section 3"`.
It imports Atomicity and BallSupport. The coordination root imports this
library together with the unchanged pinned Special transformations project.
The first checkpoint passed the library build and 22 helper-theorem type/axiom
checks; `VERIFICATION.json` binds that evidence to the actual source hashes.

Next mathematical target: finish Lemma 3.2 by connecting `finite_splitters`
to the actual ACVF definable family of disjoint balls and its imaginary codes.
The finite exceptional set must be definable over the original base. Its
finiteness then gives algebraicity of every exceptional code. Do not replace
this missing bridge by assuming that nonalgebraic balls are atomic.

Then address Lemma 3.3 (adjoining Gamma parameters), and Lemma 3.4 for open
and closed subballs of a complete-type-generating subset. Retain actual
parameter support throughout. Consult STATUS.md before the later Lemma 3.11
headline because its printed statement needs a nonemptiness qualification.

Run `lake env python3 'section 3/verify.py'` and inspect its complete logs and
headline axiom records. Compiler evidence belongs in
`.scratch/section3-verified/`, and status must distinguish generic components
from the full numbered statements still open.
