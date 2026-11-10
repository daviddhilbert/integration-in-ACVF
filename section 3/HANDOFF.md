# Continue Sections 1–3

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md, REUSE-SURVEY.md and the
predecessor LANGUAGE-ERRATA.md. Work from arXiv:0809.0473v2 through 3.24.
The user wants continuous work and has authorized pushing. No subagents
are authorized. HK may be consulted for ideas, but must not be cited or
used as an unproved formalization input.

The integrated proof checkpoint 61f65399e4c10915b36bfcaf794d7383b984c962
passed its full build, inherited foundation audit, two Section 2 audits and
471 Section 3 type/axiom audits in CI run 42884025168. There are 270 generic
and 201 actual ACVF heads. All 111 new generic complete types were reviewed;
the full output matches the local audit. The 201 unchanged actual complete
types match the earlier reviewed checkpoint exactly. Only the three standard
axioms occur. Every receipt input hash matches the proof commit.
VERIFICATION.json records the full checkpoint; CORE-VERIFICATION.json also
retains the preceding fresh local generic audit.

The new core components are DefinableHoleRefinement, AffineHoleClosure,
AffineHoleFormulas, PuncturedSupport, AtomicPuncturedPartition,
ImaginaryBaseImages, FibreSupportFormulas, AtomicFiniteFibres,
ProperInverseSupports, FiniteCofiniteClasses, QuotientCover, FiniteClosedHull
and CoverRadiusFormulas. See STATUS.md for exact mathematical scope.
Atomicity itself gives a uniform finite-row bound, so the present 3.11
route does not need a new saturation or smallness premise.

Checked numbered results remain 3.2, 3.3, 3.4, 3.7, 3.9 and 3.10 with their
explicit standing hypotheses; Section 2's 2.15 is checked, 2.34 is open.
Primitive classification 3.6, image result 3.8, corrected 3.11 and later
geometry remain open. Retain the user-approved A nonempty in 3.11.

Local uncompiled actual drafts live in the primary continuation workspace,
not this publication checkpoint. The actual radius graph and common radius
must compile first; then fixed-radius hole enlargement, affine hole closure,
primitive decomposition and primitive images can be connected. For 3.11,
connect proper inverse supports to their intrinsic ordinary closed-hull
radius, apply 3.3 to make that radius constant on target maximal classes,
and contradict their finite/cofinite definable traces with a source cut
having infinitely many smaller quotient classes on both sides.

Keep uncompiled drafts local. Compile each affected batch before push and
use CI to confirm integration. The pinned Mathlib cache is blocked in this
environment; a bounded source build is preparing its full import. Do not
route the blocked cache through CI artifacts or other hosts. Freeze all
original-model data before binding a normalized structure. Never add a
chosen centre or code representative to the exported parameter base.


## Current local continuation

Branch section-1-3/ordinary-separation starts at main's verified receipt
commit 009543e. The original local branch section-1-3/parametric-atomicity
is preserved at c3c04e9. No work was discarded. Local source changes have
276 checked generic heads and 216 proposed actual heads (15 new radius
drafts), for an unverified full total of 492. The six new generic complete
types are in .scratch/separation-six-types.txt, and CORE-VERIFICATION.json
binds all 58 current inputs. Do not push these actual drafts before passing
local compilation and type/axiom review.

The bounded Mathlib builder remains active: .scratch/build_mathlib_local.py,
PID 107163; .scratch/mathlib-local-build.log. The old waiting full verifier
was deliberately stopped before changing the base. Restart
.scratch/finish_local_verification.py at the clean continuation commit;
it first waits for Mathlib, then runs the full build, foundation audit,
Section 2 audit and Section 3 --acvf audit. Inspect its stage before edits.

Additional actual draft dependency order:
BallEnlargementGeometry; NamedClosedHoleCut; AffineArithmetic;
AffineHoleGeometry; AffineHoleCut; PrimitiveDecomposition;
PuncturedImageComponents; PrimitiveImages. For 3.11 then:
FullRelationSupports; FullGammaFamilyConstancy; SupportHullRadius;
MaximalSubballGeometry; MaximalSubballFamilies; InfiniteOrdinaryBalls;
NativeBallHulls; UniformSupportHull; ClosedTraceFamilies;
OrdinarySeparation. All these files are ignored .scratch drafts, not
compiled or counted. Register them only while no compiler is checking the
same sources, compile each affected module and inspect every exported type.

OrdinarySeparation now assembles the proposed geometric contradiction for
an ordinary open source and an ordinary closed target with finitely many
maximal open holes. Its second wrapper adjoins the target radius using
checked 3.3, so original-base radius definability is not assumed. Remaining
packaging must cover the paper's closed-ball and thin-annulus definitions,
and the vacuous whole-VF source case. Keep A nonempty explicit. The actual
proof is not established until compilation and the full audit pass.
