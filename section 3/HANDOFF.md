# Continue Section 3 here

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md and REUSE-SURVEY.md.
The source is arXiv:0809.0473v2, not OpenMathOS. Section 1 is introductory;
Section 2's Corollary 2.15 is checked, while Corollary 2.34 remains open.
This section ends at Proposition 3.24.

The full project build, inherited foundation audit, two Section 2 audits and
360 Section 3 audits passed at source `2a3b835c341e28f1662441bb84c1f8cda89b5fbe`
in [CI run 42845510919](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/42845510919).
The complete new types and axioms were reviewed, including the original-model
carriers and normalized raw definability. All receipt input hashes matched
the committed source. `VERIFICATION.json` binds this full checkpoint;
`CORE-VERIFICATION.json` retains the local 159-declaration core audit.

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

The kind predicates now have full original-base definability proofs in
BallKindPredicates.lean. AtomicCanonicalRegions.lean proves uniform
puncture status and uniformity for arbitrary definable parent properties.
BallRadiusGeometry.lean and PaperBallInvariants.lean prove actual radius
existence/uniqueness, including singleton and VF, with `δ > 1` explicit
for uniqueness. ValuativeCentreGeometry.lean proves existence on balls and
uniqueness on nonempty VF sets. These steps are fully checked.

`OrdinaryCentreFibres.lean` and `UniformValuativeCentre.lean` are checked:
full ordinary-RV centre graph, finite original-base Gamma image, individual
ordinary values and parent tests, and a common actual centre on all the
canonical positive parents of a definable complete type (including infinity
and the empty-family case). This finishes the centre-constancy component
of 3.6, not the primitive classification.

Next: the corresponding ordinary radius graph, finite image and common
radius; then nonmaximal-hole enlargement and the multiple-hole argument.
Corollary 3.7 is now checked in SameRadiusCoverage.lean, directly from
Gamma-atomicity and definable whole-coset coverage, with all ordinary,
singleton and VF cases. It uses no primitive classification. ACVF(0,0)
and an original-base definable nontrivial Gamma value remain explicit.
Use all code preimages over B; no chosen component is assumed B-definable.

For 3.11 retain the accepted explicit `A ≠ ∅`; see PAPER-CORRECTIONS.md.
Geometric separation and later results through 3.24 are still open.

Use `lake env python3 'section 3/verify.py' --acvf` for the full current audit.
Freeze original-model functions, sets and carriers before introducing any
local normalized structure. No chosen real representative may enter the
exported imaginary base. Keep scratch work and diagnostics in `.scratch/`.
