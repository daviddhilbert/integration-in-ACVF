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
and Sections2–6 succeeded; Section 7 has no verifier. The final Section 6
project pass reaudited every full type and exact artifact identity, reusing
733 certified artifacts. The preceding selected pass freshly compiled the
last module and Library. Evidence is in `.scratch/section6-final-733/`,
`.scratch/section6-final-project-audit.log`, `.scratch/section6-final-root.log`
and `.scratch/ci-verified/summary.json`. All requested work is complete in
its recorded finite-category scope.

Final entry points:
* `FiniteRV.lemma_6_17`, `FiniteRV.proposition_6_18`
* `FiniteRV.theorem_6_19` and its class characterization
* `FiniteRV.IntegrationContext.functionModule`, `.integralLinearMap`
* `FiniteRV.remark_6_20_linearity`
* `coordinatePushforward`, `coordinatePushforward_value`,
  `coordinatePushforward_integral`, `proposition_6_21`
* `FiniteRV.theorem_6_22`, `_injective`, `_lift`, `_graded_colimit`

All names are under `IntegrationInACVF.Section6`; the full import is
`IntegrationSection6.Library`. STATUS.md and TARGETS.md give precise coverage.
No implementation or verification step remains.

Preserve the stash `section 6 active formalization before upstream sync`.
No dependency changes or subagents were used. After verification, the user
authorized committing and pushing the completed state to origin/main.
