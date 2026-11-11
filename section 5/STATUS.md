# Section 5 status

Work started on branch `section-5/contracting-to-rv` from `c8f4270`.
The section's precise targets and scope are in TARGETS.md.

**Lemma 5.1 is locally checked**, over a small real base and over the original
real/Gamma base with the explicit VF coefficient-field scope. The complete
121-declaration type/axiom audit passed; only propext, Classical.choice and
Quot.sound occur. Its exact source receipt and full type output are retained
in `.scratch/section5-verified/`. The full root build and project audit also passed.
The constructed 5.2/5.4 supporting geometry is included in that audit; neither
5.2 nor the full section is claimed complete.

| Module | Locally checked scope |
| --- | --- |
| `Preparation` | Lemma 5.1, small real base, all finite mixed arities. Uses the actual predecessor preparation and its proved obstacle producer. |
| `GammaPreparation` | Lemma 5.1 over the original real/Gamma base with a common working real presentation, retaining complete invariant transformation and conjugate graphs. The shared-presentation wrapper is drafted separately in GammaMapPresentation. |
| `GammaMapPresentation` | Constructs a common real presentation internally and states the set-level Lemma 5.1 over the original Gamma base. No code-set smallness premise. |
| `QuotientBijection` | The induced RV-key map of a contractible bijection is bijective iff its actual inverse is contractible. A unique definable commuting bijection follows with that explicit premise. This is the final quotient step, not 5.2. |
| `RelativelyUnary`, `UnaryFactorizations` | Coordinate-preservation predicate; actual finite chains of definable relatively unary bijections; factorization of every supplied special bijection in positive VF arity; the arity-one base case of 5.6. Relative specialness and full 5.6 remain open. |
| `UnaryBallImages`, `UnaryTranslations` | A zero-free actual open polydisc lies in one RV class; the centred open-image contractibility criterion and translation calculus. |
| `FocusSection`, `PulledFocusGeometry`, `PulledFocusDefinability` | An actual target focus section, selected source RV-cell locus, source centre, full original-real-base graphs, and a constructed source Focus. The supplied map is assumed contractible; no compatible-transformation conclusion is assumed or claimed. |

The section library and separate geometry entry point are registered in
Lake. The fresh 121-declaration build/type/axiom batch passed. Full types,
source/pin hashes and audit identities are recorded in VERIFICATION.json.
The full root integration build and project audit passed: foundation and
Sections 2, 3 and 5. The proof checkpoint is ready for CI confirmation.

The full pinned dependency build completed successfully (9294 jobs). The
cache denial has therefore been overcome by an actual from-source build;
no network-setting change is required to proceed. Local checks use Lean
4.35.0 and all 11 package revisions match the committed manifest.

Active proof work: target focus-section construction, the pulled source
locus and its original-base graph, and the unary-chain factorization of
actual special bijections. The open-ball geometric criterion is checked
individually: a centred map with actual open nonzero RV-cell images is
contractible. Both matched-focus directions, open-image preservation and the zero-marker
chain argument now compile and pass the 121-head audit. The full compatible
chain induction, original-Gamma graph certificates and 3.21 partition
assembly remain to be proved.

No Section 5 result is assumed as a prerequisite of itself. No HK or referee
result is cited. No paper correction has been silently adopted. Definitions,
partial scopes, conditional consequences and proved numbered results must
continue to be counted separately.

The first wider root build completed from the existing Mathlib/predecessor
artifacts while freshly building the remaining pinned/project modules
(10218 jobs reported). The matched-focus root consumer build then passed
(10236 jobs, largely artifact reuse). Both are local checks; remote CI
confirmation is a separate publication step. All 72 previous complete types
are unchanged in the 121-head audit.
