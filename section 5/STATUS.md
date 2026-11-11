# Section 5 status

Work started on branch `section-5/contracting-to-rv` from `c8f4270`.
The section's precise targets and scope are in TARGETS.md.

**No new theorem is certified yet.** The initial Lean proof batch is local
and awaiting compilation, complete exported-type review and axiom audits.

| Module | Draft scope |
| --- | --- |
| `Preparation` | Lemma 5.1, small real base, all finite mixed arities. Uses the actual predecessor preparation and its proved obstacle producer. |
| `GammaPreparation` | Lemma 5.1 over the original real/Gamma base with a common working real presentation, retaining complete invariant transformation and conjugate graphs. The shared-presentation wrapper is drafted separately in GammaMapPresentation. |
| `GammaMapPresentation` | Constructs a common real presentation internally and states the set-level Lemma 5.1 over the original Gamma base. No code-set smallness premise. |
| `QuotientBijection` | The induced RV-key map of a contractible bijection is bijective iff its actual inverse is contractible. A unique definable commuting bijection follows with that explicit premise. This is the final quotient step, not 5.2. |
| `RelativelyUnary` | Definition 5.4's coordinate-preservation predicate, inverse and composition rules, one-coordinate case and canonical bijection case. Relative specialness is not yet encoded. |

The section library is registered in Lake. Root integration will follow
successful local verification; uncompiled drafts have not been pushed.

The current environment initially had no Lake package artifacts. The exact
pinned packages were materialized and Lean/Lake 4.35.0 was checked. Cache
download hit a read-only default cache path; redirecting `XDG_CACHE_HOME`
to `/workspace/.cache` fixed that issue. Download then received an actual
proxy 403 for `cache.mathlib.org`; network-settings input was requested.
The denied download was stopped. The broad predecessor build and initial
Section 5 build were interrupted deliberately (exit 130) to target the actual
prerequisite modules first, retaining their completed artifacts.
`lake build Section5.GammaInvariantLogic Section5.GammaContraction` is now
running. Its source closure contains roughly 9,000 modules because of the
foundation's whole-Mathlib import; a cache download remains the practical
way to finish local verification promptly. Logs are in `.scratch/cache-get.log`,
`.scratch/predecessor-build.log`, `.scratch/section5-build.log` and
`.scratch/section5-dependencies.log`. The allowlist request is still pending.

No Section 5 result is assumed as a prerequisite of itself. No HK or referee
result is cited. No paper correction has been silently adopted. Definitions,
partial scopes, conditional consequences and proved numbered results must
continue to be counted separately.
