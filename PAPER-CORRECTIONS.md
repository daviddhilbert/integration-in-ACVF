# Corrections and checked boundaries in arXiv:0809.0473v2

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

## Lemma 4.3: allow an empty radius set

Author clarification in the section 4 chat, November 11, 2026
(America/Los_Angeles): replace “is a singleton” by **“has at most one
element”** in the displayed set of source radii.

The identity on an ordinary open ball of radius beta has no subball with
image radius alpha when alpha<beta. The radius set is empty on every
possible inverse piece of a special preparation. The corrected conclusion
allows this empty case without adding a restriction on alpha.

The author explicitly approved this correction. Corrected Lemma 4.3 is
now proved by RadiusPreparation.lemma_4_3; the independent actual-ball
boundary is proved in RadiusBoundary. Exact verification is recorded under
section 4.


## Checked boundary after Definition 4.7: singleton first projection

The unnumbered sentence claims that a nonbalanced 2-cell with nonzero
paradigm is an open polydisc. Definition 4.7 also allows its first 1-cell
to be a singleton. The actual definable cell
`{1} × rv⁻¹(rv(1))`, with constant positioning function `0`, has nonzero
paradigm and is not balanced, but its singleton first projection is not
an open ball. Definition 2.2's open-polydisc convention therefore excludes it.

OpenPolydiscBoundary.definable_cell, nonzero_paradigm, not_balanced and
not_open_polydisc prove these assertions independently on the pinned native
carriers. The definable-cell theorem works over any original Gamma base;
the no-open-singleton conclusion uses ACVF00 and an explicit nontrivial
Gamma value. No referee assertion is a proof input.

Two precise replacements are already proved: CellRectangles.rectangle
says the cell is a product of its first 1-cell and an open ball;
CellRectangles.open_polydisc adds the hypothesis that the first projection
is open. The author's wording choice was requested in the section 4 chat
and is pending. This entry records a verified boundary, not an approved
change to the printed sentence. Definition 4.7 and Lemma 4.8 are unchanged.
