# Pending statement clarifications

## Proposition 3.24: the whole-field parent

**Author approval is pending. No correction has been adopted.**

Original Definition 2.2 calls VF clopen, with radius minus infinity.
Under that convention, take the same parent VF and remove the same proper
ordinary open ball in both source and target. The two resulting punctured
balls coincide, so the identity is a definable open-to-open bijection.
Their body is nonempty. This contradicts the literal boundary scope of3.24.

The independent Lean theorem is
`Proposition324WholeFieldBoundary.counterexample` in
[the checked source](section%203/IntegrationSection3ACVF/Proposition324WholeFieldBoundary.lean).
It constructs the actual punctured ball, one proper open hole, a nonempty
body, a finite real parameter base, exactly one original Gamma name for
an arbitrary nontrivial value, the full identity graph, actual bijectivity,
and actual OpenToOpen. It uses only propext, Classical.choice and Quot.sound.
The1051-head local root/type/axiom audit includes it; CI is pending.

The author was asked whether3.24 should require the **closed parent to be
ordinary, with radius in Gamma**, excluding VF. No answer has yet arrived.
This is a proposed statement clarification, not an inferred approval.
The ordinary-parent obstruction still requires induced RV/Gamma maps and
an independently proved definable interval-bijection obstruction.

This boundary check was developed independently from the paper's definitions.
No referee assertion, suggested repair, new citation or HK theorem is an input.
It is separate from the earlier finite-radius endpoint calculation recorded
in REFERENCE-NOTES.md.
