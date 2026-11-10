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
