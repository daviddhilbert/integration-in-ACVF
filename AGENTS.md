# Working agreement

Read [WORKFLOW.md](WORKFLOW.md) before substantive work. Preserve unrelated edits.
The numbered folders are for sections of arXiv:0809.0473v2, not the predecessor.

Use the pinned Special transformations and ACVF-QE dependencies; reuse their
language and definitions rather than copying or restarting the earlier proofs.
Read the predecessor's LANGUAGE-ERRATA.md and relevant section status before
relying on its mathematical results. A dependency pin is not a claim that every
statement of that paper is proved without explicit hypotheses.

Preserve its conventions: RV has one absorbing element, Mathlib's multiplicative
valuation order reverses the paper's order, and equal valuation does not mean
equal RV class. Keep the actual parameter base, characteristic and saturation
assumptions visible. Do not define saturation by the conclusions being sought.

A completed result requires compilation, inspection of its full theorem type
and an axiom audit allowing only propext, Classical.choice and Quot.sound.
Do not count a theorem assuming an open obligation as a proof of that obligation.
Record conditional results and coverage precisely. Keep scratch output in
.scratch/. Publish within the user's authorization.

Citation policy (user clarification, November 10, 2026): citations outside the
approved list require user approval, except results already formalized.
Check the existing Lean theorem and its hypotheses before using that exception.
