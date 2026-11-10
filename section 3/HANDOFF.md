# Continue Section 3 here

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md and REUSE-SURVEY.md.
The source is arXiv:0809.0473v2, not OpenMathOS. Section 1 is introductory;
Section 2's Corollary 2.15 is checked, while Corollary 2.34 remains open.
This section ends at Proposition 3.24.

The full project build, inherited foundation audit, two Section 2 audits and
288 Section 3 audits passed at source `a401f0579918de5ff128f723b98e39aecd5ca416`
in [CI run 42829855150](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42829855150).
The complete new types and axioms were reviewed, including the original-model
carriers and normalized raw definability. All receipt input hashes matched
the committed source. `VERIFICATION.json` binds this full checkpoint;
`CORE-VERIFICATION.json` now records the 147-declaration local core continuation.

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

Next: Lemma 3.6's definable positive-region family. Define strict ball
containment and region membership over the same base by quantifying all
candidate real codes, then recover the finite positive-parent family.
Radius, valuative centre and kind must be actual invariant Gamma/ball
predicates. Nonmaximal-hole enlargement and the integer-translate argument
for multiple maximal holes remain open. Reuse the checked integer-unit and
coset geometry from the proof of 3.9 where applicable. No component itself
is assumed definable over the original base.

For 3.11 retain the accepted explicit `A ≠ ∅`; see PAPER-CORRECTIONS.md.
Geometric separation and later results through 3.24 are still open.

Use `lake env python3 'section 3/verify.py' --acvf` for the full current audit.
Freeze original-model functions, sets and carriers before introducing any
local normalized structure. No chosen real representative may enter the
exported imaginary base. Keep scratch work and diagnostics in `.scratch/`.

Current continuation: `RegionFormulas.lean` passed all nine new full types and
standard-axiom checks locally (142 core total). `CanonicalRegions.lean` now
implements the actual positive-family and disjoint-decomposition bridge,
awaiting full CI. Next define the original-base maximal-hole relation and
then the invariant radius/valuative-centre/kind graphs.

`HoleFormulas.lean` passed its five new full type/axiom checks (147 core
total). `CanonicalHoles.lean` supplies the full interpreted pair-of-balls
relation. The previous actual CI found use of the whole presentation proof
where code-domain definability was required; the revised region/hole calls
now use `codeDomain_definable`. Full CI remains required.
