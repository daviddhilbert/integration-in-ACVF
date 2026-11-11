# Accepted corrections to arXiv:0809.0473v2

## Lemma 3.11: nonempty relation

Author clarification in this session, November 10, 2026
(America/Los_Angeles): add the hypothesis `A ≠ ∅`.

The corrected target is: let `o` be an atomic open ball and `l` an atomic
closed ball of finite radius or an atomic thin annulus. If `A ⊆ o × l` is
definable **and nonempty**, its first projection is not finite-to-one.

The empty relation satisfies definability, containment in every product,
and finiteness of every first-projection fibre. This obstruction is checked
in `section 3/IntegrationSection3/StatementChecks.lean`. The proof printed in
the paper uses surjectivity of both projections; atomicity gives this only
after nonemptiness is known.

This approves the corrected hypothesis. It is not a claim that the corrected
Lemma 3.11 or its geometric prerequisites have already been proved in Lean.

## Proposition 3.24: ordinary closed parent

Author clarification in this session: **exclude VF as the closed parent**.
The closed parent must be an ordinary closed ball with radius in Gamma.
The target's open parent retains the paper's convention, including VF.

The corrected target is: let f be a definable bijection from an ordinary
closed ball with one proper open hole removed onto an open ball with one
proper open hole removed. Then f cannot have the open-to-open property.

Definition2.2 calls VF clopen. If both parents are VF and the same proper
ordinary open hole is removed, the identity is a definable open-to-open
bijection on a nonempty body. This boundary counterexample is checked in
Proposition324WholeFieldBoundary.counterexample. It retains a finite real
base and an originally named nontrivial Gamma value.

The author explicitly approved the ordinary closed-parent restriction.
The corrected proposition is now proved by
PuncturedBallObstruction.proposition_3_24. Exact actual quotient graphs and
the independent Gamma interval obstruction supply every input. Standing
genuine saturation,infinite cardinal,small real base andACVF00 are explicit.
