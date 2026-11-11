# Section 5 continuation

Read ../AGENTS.md, ../WORKFLOW.md, TARGETS.md, REUSE-SURVEY.md and STATUS.md.
This chat follows the workflow recovered from “section 1-3”, including local
compilation before publication and exact type/axiom/source evidence.

Initial branch: `section-5/contracting-to-rv`; starting main: `c8f4270`.
The section currently contains uncompiled local drafts only. Do not report
them as proved and do not publish them before successful local checks.

Next:

1. Finish the pinned dependency build. Activate Lean with
   `source /workspace/.tools/activate-lean.sh`. Use
   `XDG_CACHE_HOME=/workspace/.cache` for cache commands; the cache host was
   proxy-blocked and the user was asked to allow it in environment settings.
   A targeted from-source dependency build is running in
   `.scratch/section5-dependencies.log`; earlier broader builds were
   interrupted deliberately and their artifacts retained.
2. Build `IntegrationSection5`. Fix actual compiler diagnostics; inspect full
   exported types and audit every new declaration with `#print axioms`.
   Only propext, Classical.choice and Quot.sound are permitted.
3. Check `GammaMapPresentation.common_gamma_presentation` and `lemma_5_1`,
   which now draft the complete set-level wrapper by combining domain and
   graph codes internally. Original-base graphs and VFFieldBase are explicit.
4. Integrate the locally checked library at the root, run the root build,
   foundation/Section2/Section3/Section5 verifiers, and record exact scope.
5. Continue 5.2's compatible unary transformations, using checked 3.21 and
   the actual predecessor inverse-fibre geometry. Inverse contractibility
   is the work still required; the quotient criterion does not discharge it.

The 2-cell and standard-contraction targets remain open. Coordinate with
the section 4 repository changes through current source/status, without
silently assuming its results. Keep substantially different mathematical
proofs in the whole-paper PROOF-WRITEUP.md ledger when established.
