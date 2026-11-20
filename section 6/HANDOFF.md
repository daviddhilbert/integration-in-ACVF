# November 15 integration update

The completed Section 5 branch is integrated. Three checked modules
(`CompletedSection5Comparisons`, `CompletedSection5Refinements`,
`CompletedSection5TwoOrderInput`) now prove the actual two-order input over
each base satisfying the displayed standing hypotheses of 5.8, with no
5.8 assumption in that producer. All five exported types and axiom reports
were reviewed; the affected Library and root import build. The registered
boundary is **736 modules and 2,273 exports**. Evidence is versioned under
`verification/completed-section5/`.

The older final integration interface `Section5TwoOrderInputAll` still
quantifies over arbitrary frozen parameter bases and is not discharged by
this fixed-base producer. *(Updated November 19, 2026: it remains
undischarged, but it is no longer needed. The closed entry points in
`IntegrationInACVF.Section7.CompletedSection6`, listed below, prove
6.16–6.22 over the standing VF/Gamma-generated base without it. Only the
legacy conditional `FiniteRV` interfaces still assume it.)*
The historical scope and evidence below describe the prior 733-module run.
Section 7 now has its own verifier; older statements that it has none are
historical. See the root PROJECT-AUDIT.md for the current project boundary.

---

# Section 6 — completion verification

All numbered Section 6 targets are implemented for RV[k] and graded RV[*].
The finite-volume condition concerns the volume map, not domain cardinality.
RV[k,·] is abandoned. Native lifting retains genuine VF/Gamma generation;
no canonical-presentation restriction remains. The only unfinished numbered
input is the explicit, user-authorized Section 5.8 refinement
`Section5TwoOrderInputAll`. No6.x statement is assumed.

The complete certificate covers 733 modules and 2,268 full type/axiom checks;
the root build passed 11,202 jobs. Only propext, Classical.choice and Quot.sound
occur; no proof drafts are excluded. The project-wide command
`lake env python3 scripts/verify_ci.py --reuse-certified` passed: inherited QE
and Sections2–6 succeeded; Section 7 had no verifier at the time (it has one now). The final Section 6
project pass reaudited every full type and exact artifact identity, reusing
733 certified artifacts. The preceding selected pass freshly compiled the
last module and Library. Evidence is in `.scratch/section6-final-733/`,
`.scratch/section6-final-project-audit.log`, `.scratch/section6-final-root.log`
and `.scratch/ci-verified/summary.json`. All requested work is complete in
its recorded finite-category scope.

Final entry points *(updated November 19, 2026)*: use the closed theorems
in `IntegrationInACVF.Section7.CompletedSection6` (import
`Integration7.Library`), which assume no Section 5.8 premise:
* `CompletedSection6.lemma_6_16`, `CompletedSection6.lemma_6_17`
* `CompletedSection6.proposition_6_18`, `CompletedSection6.theorem_6_19`
  and its class characterization
* `CompletedSection6.IntegrationContext.functionModule`, `.integralLinearMap`
* `CompletedSection6.remark_6_20_representative_independence`,
  `CompletedSection6.remark_6_20_linearity`
* `CompletedSection6.coordinatePushforward`, `_value`, `_integral`,
  `CompletedSection6.proposition_6_21`
* `CompletedSection6.theorem_6_22`, `_injective`, `_lift`, `_graded_colimit`

The November 12 entry points below, under `IntegrationInACVF.Section6`
(import `IntegrationSection6.Library`), are the **conditional** legacy
interfaces. Their 6.16–6.22 results assume the universal Section 5.8
premise (`h58` / `Section5TwoOrderInputAll`), which is not discharged:
* `FiniteRV.lemma_6_16`, `FiniteRV.lemma_6_17`, `FiniteRV.proposition_6_18`
* `FiniteRV.theorem_6_19` and its class characterization
* `FiniteRV.IntegrationContext.functionModule`, `.integralLinearMap`
* `FiniteRV.remark_6_20_linearity`
* `coordinatePushforward`, `coordinatePushforward_value`,
  `coordinatePushforward_integral`, `proposition_6_21`
* `FiniteRV.theorem_6_22`, `_injective`, `_lift`, `_graded_colimit`

STATUS.md and TARGETS.md give precise coverage. With the closed entry
points above, no Section 6 implementation step remains in the recorded
scope; the conditional interfaces are retained with unchanged types.

Preserve the stash `section 6 active formalization before upstream sync`.
No dependency changes or subagents were used. After verification, the user
authorized committing and pushing the completed state to origin/main.
