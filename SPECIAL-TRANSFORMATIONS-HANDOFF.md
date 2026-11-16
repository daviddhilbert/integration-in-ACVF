# Handoff: weighted measured degree zero in Special transformations

Prepared for the Special transformations session. The author will carry
out that repository's implementation there; this Section 7 session owns
the subsequent changes in integration-in-ACVF.

## Objective and authorization

The author approved adopting HK's measured degree-zero convention in both
repositories. Correct the degree-zero exceptions in Definitions 10.1 and
10.3 of arXiv:1006.2467v1, within the repository's existing finite-volume
scope. Extend the affected Section 10 results to those corrected categories.

This adopts a convention, not unproved HK theorems as Lean inputs. The
primary comparison is HK, arXiv:math/0510133v3, Definitions 8.10 and 8.13.
Reprove the required consequences using the checked common language and
existing library. The author explicitly narrowed the review to the scope
of the two papers.

## Exact accepted convention

- **µRV[0]:** a finite-volume ordinary zero-degree RV object together with
  an actual definable nonzero RV-valued form. Isomorphisms preserve the
  exact RV weight at every point.
- **µVF[0]:** retain the analogous definable nonzero RV form on the
  ordinary zero-degree VF object. Its measured isomorphisms preserve the
  exact weight. Use the existing zero presentation or a proved equivalent
  presentation; do not silently restrict its objects.
- **Gamma-valued counterparts already in Section 10:** retain definable
  Gamma-valued forms at zero, with exact equality in Gamma. Distinguish
  these from RV-valued forms: equal valuation is not equal RV class.
- The empty-coordinate Jacobian is 1. No nonempty degree-zero locus may
  be discarded as an exceptional set of dimension below zero.
- Ordinary RV[0]/VF[0] remain unchanged. Their neutral-form embeddings
  recover the measured neutral-form zero subcategories.
- Forms multiply under products, including zero factors. The neutral
  Gamma weight is 1 in the library's multiplicative notation, corresponding
  to additive 0 in the paper. Form pullback must retain the supplied form.

Keep the single absorbing RV element, valuation order convention, actual
parameter base, finite-volume conditions, characteristic and saturation
hypotheses. No definable section from Gamma to RV is being assumed.

## Scope boundaries

In scope are the existing measured RV/VF categories, their RV-valued and
Gamma-valued forms, the zero cases of 10.4–10.6, restrictions, scissors,
additive lifts, neutral-form specializations and graded category assembly.
Preserve the existing positive-degree results and their hypotheses.

HK's pure value-group categories, RES categories and RES–Gamma tensor
decomposition are **outside scope**. Their absence is not an unfinished
obligation of either repository. A general new coarsening-functor package
and a global commuting-square theorem are also not extra completion targets.
Check passage to Gamma values only where an existing construction uses it.

Section 7's blowup kernel, point/cone principal ideal, function integration
and normalization belong to integration-in-ACVF, not to this handoff's
implementation. No new mathematical change to Special transformations
Sections 2–9 was identified as necessary for the zero convention.

## Reviewed source boundary

The review inspected Special transformations main at
`f76d100e07c0a791259244fc7fdf06f4dfaaf8ae`. Its active Section 10 proof
checkpoint is `7f2e697c8cfcb2702504f78ef3cc79289f040179`, with 18 active
modules. This is the completed Section 10 implementation under the old
measured-zero convention, not merely the historical scaffold.

The receiving session should use its own current worktree and preserve any
newer work. These SHAs identify the reviewed sources, not a request to reset
that session or overwrite its changes.

The inspected toolchain and dependencies were:

- Lean `leanprover/lean4:v4.35.0`.
- Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- ACVF-QE `939346b0a99899e22a873479364e3cc5d142731c`.

## Concrete changes identified

| File under Section10/ | Current behavior and required extension |
| --- | --- |
| `GradedCategories.lean` | `VFInDegree` and `RVInDegree` hardcode ordinary zero categories. Supply weighted zero categories for the appropriate form scale. Parameterize the generic RV assembly's zero category, or use an all-degree family, so RV and Gamma forms are both retained. |
| `ZeroDegree.lean` | `theorem_10_4_zero`, `theorem_10_5_zero` and `corollary_10_6_zero` concern ordinary objects/classes. Preserve them as ordinary results and establish the actual weighted versions for both form scales. |
| `MeasuredVFCategory.lean` | `VolumeScale` already unifies RV and Gamma form data, but `MeasuredVF` is indexed by actual degree `k+1`. Reuse the scale abstraction for zero objects and exact weight-preserving bijections. Positive independent-point germs need not be rebuilt to handle zero. |
| `MeasuredScissors.lean` | `MeasuredRV` and its lift are also positive-degree constructions. Extend empty objects, restriction of the same form, scissors and form-preserving zero lift. |
| `MeasuredPositiveLift.lean` | Reuse positive proofs. Establish the zero measured additive lift with its actual generator formula and surjectivity. |
| `UnitVolume.lean` | Identify the new neutral-form zero categories with the existing ordinary zero categories, retaining positive unit-form results. |
| `Library.lean` and audit selection | Register the new actual zero definitions and headline types/axioms, then integrate the affected categories and theorem wrappers. Update status and handoff to distinguish old ordinary results from new measured ones. |

`RVVolumeLift.lean` already defines a form on an arbitrary definable domain;
its positive `RVVolumeObject`, `GammaVolumeLift.lean`'s positive
`GammaVolumeObject`, and the positive isomorphisms are reusable. Existing
positive indices named `k` mean degree `k+1`. Keeping their API stable is
preferable to renumbering every positive theorem.

For 10.4 at zero, transport the given form through the existing ordinary
finite lift presentation. For 10.5, retain the supplied label isomorphism
and prove the pulled-back forms agree, using empty-coordinate determinant
1. For 10.6, descend that construction through weighted isomorphism and
scissors relations. These are proposed proof routes, not newly checked
proofs. Section 9 already supplies zero-arity Jacobian facts.

The positive RV lift retains its documented
`FiniteHenselianExtensionReference` premise. This convention change does not
discharge that premise. The sequel's independent field-theoretic proof is
not automatically an imported result in this repository. No such positive
graph-field premise is indicated for the new zero cases.

Do not use `Sec10.lean`, `Sec10RVVol.lean` or
`LegacyScaffold/VolumeForms.lean` as a second implementation: they are
historical sources with obsolete interfaces and explicit assumed inputs.

## Interfaces needed by integration-in-ACVF

Export or document the actual names/types of:

1. Weighted zero RV and VF objects, their exact isomorphisms, underlying
   objects and form values, for both existing form scales.
2. Form pullback/restriction and the ordinary neutral-form embeddings.
3. The form-preserving zero lift, its invariance and zero 10.4–10.6 results.
4. The revised all-degree category assembly and its zero/positive adapters.

Where product/form operations are exported, expose their pointwise density
formula. The sequel needs to prove mixed graded multiplication retains
both densities; this does not require building its entire graded semiring
or integration theory in Special transformations.

The sequel will adapt these interfaces in its Sections 2 and 7. Its
current pin is `9cc9760892092dd34cfad4a6dee655843c52f30c`, which predates
the 18 active Section 10 modules. Do not assess the current predecessor
from that stale snapshot. Conversely, current main has other changes to
earlier geometry relative to that pin, so consuming the corrected revision
requires a downstream compatibility build or a suitable backport. This
handoff does not change the sequel's dependency pin.

Return a checked commit SHA, the relevant exported interface names, build
and audit scope, and any changed hypotheses. The Section 7 session will
perform the downstream adaptation and dependency integration.

## Verification and work already performed

This session performed source/dependency review and documentation edits
only. **No Lean source was modified for this migration, and no new theorem
was compiled or audited.** Existing positive and ordinary-zero verification
receipts remain evidence for their original types. They do not certify the
new weighted targets.

Compile coherent affected batches, inspect the complete new theorem types,
and audit axioms against `{propext, Classical.choice, Quot.sound}`. Check
actual weighted preservation and standing hypotheses, not merely an axiom
allowlist. Use the repository's existing targeted checks:

```sh
lake -R build Section10
lake env python3 scripts/verify_ci.py section10
```

After affected checks pass, check the project root integration. A new full
mathematical audit of unchanged earlier sections is unnecessary. Publish
only evidence matching the source revision actually checked.

## Location of review material

The isolated review checkout in this session is
`/workspace/special-transformations-hk`. Review/documentation edits there
are uncommitted and have not been pushed; its path is not assumed to exist
in the receiving session. The relevant files are `AGENTS.md`, `README.md`,
`Section10/STATUS.md`, `Section10/README.md`, `Section10/HANDOFF.md`,
`Section10/HK-CONVENTION-REVIEW.md` and
`Section10/hk-impact-inventory.json`.

This standalone handoff contains the decisions needed to continue even
without access to that checkout. Reconcile its accepted changes with the
receiving session's current documentation rather than treating a local
review copy as an implemented or published checkpoint.
