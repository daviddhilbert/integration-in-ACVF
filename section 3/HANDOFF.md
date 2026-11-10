# Continue Sections 1–3

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md, REUSE-SURVEY.md and the
pinned predecessor's LANGUAGE-ERRATA.md. Work from arXiv:0809.0473v2 through
3.24. The user authorized continuous work and pushes. No subagents are
authorized. HK is background for ideas only, with no citation or unproved input.

The current local full root build and foundation/Section2/Section3 audits pass:
551 Section3 heads, comprising 276 generic and 275 actual ACVF declarations.
Full new types were reviewed. All 201 prior actual types match the reviewed
2a3b835 checkpoint exactly; all 59 new primitive-batch types match their fresh
individual audits exactly; the 15 radius and six generic separation types
were reviewed at the preceding local 492-head check. Every source hash matches,
and only the three standard axioms occur. See VERIFICATION.json and
.scratch/local-primitive-551/. CI run42900083681 passed at proof92f7b0a; all551 complete CI types and
all105 source hashes match the reviewed local evidence. Previous
public proof61f6539 had green run42884025168 and main009543e had green
run42885111227. Do not confuse that older471-head receipt with the new batch.

Checked numbered results: 3.2,3.3,3.4 at original-base definable radii plus
singleton/VF,3.6,3.7,3.8,3.9,3.10, with the explicit hypotheses in STATUS.md.
Section2 has2.15 checked and2.34 open. There are13 remaining Section3 proof
results;3.20 is a definition. Keep author-approved R.Nonempty in3.11.

Mathlib bootstrap and the bounded predecessor preparation have finished
successfully. Do not restart them. The local root now needs only the pinned
Sections3/4 libraries and ACVFQE, while CI independently builds the full
predecessor. No dependency pin or old statement changed.

The primary continuation is /workspace/integration-in-ACVF on branch
section-1-3/ordinary-separation. The older local branch
section-1-3/parametric-atomicity remains at c3c04e9; nothing was discarded.
The previous publication worktree is /workspace/integration-in-ACVF-publish.

Next actual draft dependency order for3.11, kept in the original workspace's
ignored .scratch folder: FullRelationSupports; FullGammaFamilyConstancy;
SupportHullRadius; MaximalSubballGeometry; MaximalSubballFamilies;
InfiniteOrdinaryBalls; NativeBallHulls; UniformSupportHull;
ClosedTraceFamilies; OrdinarySeparation; Separation; SeparationFunctions;
OpenImages. FullRelationSupports has now passed its individual four-head
compile/type/axiom audit, pending manual type review. The remaining wrappers
have not been checked yet. Do not count assembled3.11–3.13 as proved.

Use .scratch/check_actual_draft.py to check an ignored module against the
local library without publishing. Its overlay must symlink existing project
artifacts and unlink any symlink for its own output before compiling. Lean
resolves a namespace from the first library directory. Review full exported
types and axioms, register a coherent stable batch, run the actual combined
build/audit, and only then push. Never edit a compiler's active input.

Extra ignored checked components beyond the registered551: generic
PolynomialSpecialization(1),FibreEqualityFormulas(2),BivariateCoordinates(3),
and actual PolynomialEscape(4). Their complete types and standard axioms were
reviewed individually. They are not in the combined count or publication.
AtomicPolynomialRoots and BallCentreElimination are uncompiled actual drafts
for3.14. See .scratch/CLOSED-IMAGE-PLAN.md. A named-radius-only wrapper for3.15
is partial scope; do not silently claim an unrestricted unnamed-radius result.

Do not add chosen centres or radius lifts to the base. No conclusion-shaped
saturation premise, new HK input or cache/network workaround is authorized.
