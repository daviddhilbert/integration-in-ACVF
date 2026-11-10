# Continue Section 3 here

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md and REUSE-SURVEY.md.
The source is arXiv:0809.0473v2, not OpenMathOS. Section 1 is introductory;
Section 2's Corollary 2.15 is checked, while Corollary 2.34 remains open.
This section ends at Proposition 3.24.

The full project build, inherited foundation audit, two Section 2 audits and
306 Section 3 audits passed at source `661d4fed208c86486a2bba7a247f2027b8c4e1fa`
in [CI run 42833098057](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42833098057).
The complete new types and axioms were reviewed, including the original-model
carriers and normalized raw definability. All receipt input hashes matched
the committed source. `VERIFICATION.json` binds this full checkpoint;
`CORE-VERIFICATION.json` now records the 156-declaration local core continuation.

Checked entry points:

- `AdjoinBall.lemma_3_2`: full real/Gamma/ball base; input-ball name adjoined;
  nonalgebraicity of the output-ball imaginary.
- `FullGammaAtomicity.lemma_3_3`: every finite Gamma tuple preserves atomicity
  in every finite real tuple arity over the combined base. ACVF(0,0),
  original-base definable `δ` and `1 < δ` are explicit.
- `FullGammaRadius.lemma_3_4`: every original-base definable ordinary Gamma
  radius, plus singleton and VF cases, over the combined base. The ambient
  complete type need not be a definable set.
- `OpenBallConstancy.lemma_3_9_open` and `corollary_3_10_open`: exact sequel
  open-ball convention, every finite RV output arity, full graph on the
  stated domain. Corollary 3.10 permits an initially unnamed subball radius.
- `PaperBalls.lean` and `PuncturedGeometry.lean`: primitive-type predicates
  and the finite disjoint punctured decomposition, without claiming 3.6's
  primitive classification.

`CanonicalSupportFamily.exists_definable_canonical_support` is also checked:
unique minimal finite support, actual ball-code coverage in both directions,
and original-base definability of its entire finite family. It reuses the
already formalized `ValOneEC.Johnson.ne_finite_union_of_proper_subballs` from
pinned ACVF-QE and derives the valuation's nontriviality from `δ > 1`.
The fixed-support positive-region decomposition is checked generically.

`CanonicalRegions.exists_definable_positive_decomposition` and
`CanonicalHoles.holes_definable` are checked: finite original-base definable
positive-parent family, original-base region membership, nonempty disjoint
bodies covering A, actual maximal proper holes and the full interpreted
hole/parent relation. Their generic formulas are in RegionFormulas.lean and
HoleFormulas.lean.

Next: Lemma 3.6's invariant radius, valuative-centre and kind predicates.
Nonmaximal-hole enlargement and the integer-translate argument for multiple
maximal holes remain open. Reuse the checked integer-unit/coset geometry
from 3.9. No component itself is assumed definable over the original base.

For 3.11 retain the accepted explicit `A ≠ ∅`; see PAPER-CORRECTIONS.md.
Geometric separation and later results through 3.24 are still open.

Use `lake env python3 'section 3/verify.py' --acvf` for the full current audit.
Freeze original-model functions, sets and carriers before introducing any
local normalized structure. No chosen real representative may enter the
exported imaginary base. Keep scratch work and diagnostics in `.scratch/`.

Current continuation: the 156-declaration generic core passed its full types,
standard-axiom audit and source-hash check. The actual modules now implement
full-code kind tests, canonical positive-region uniformity and puncture
status, ordinary/extended radius uniqueness, radius existence, and valuative
centre existence/uniqueness. They await full CI. Source-model functions and
carriers are frozen before normalization; explicitly `change` through set
membership and local aliases before rewriting. Next define invariant graphs,
prove their finite images, use atomicity for constant invariants, then finish
nonmaximal-hole enlargement and the multiple-hole contradiction.
