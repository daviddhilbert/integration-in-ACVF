# Section 4 handoff

Read AGENTS.md, WORKFLOW.md, STATUS.md, TARGETS.md and REUSE-SURVEY.md.
All five numbered lemmas (4.1–4.4 and 4.8) are proved in the recorded scope.
Definitions 4.5/4.7, their parameterized forms, Remark 4.6, balanced hulls,
ball correspondence, internal symmetry, and unary decomposition are checked.
Both statement corrections are approved: the at-most-one formulation in
4.3 and “a product of a 1-cell and an open ball” after 4.7. Both corrected
statements are proved; no Section 4 editorial question remains pending.

Main entries:
- FiniteOffsets.lemma_4_1: actual original-base offsets, finite range and zero.
- LinearPreparation.lemma_4_2: actual linear/open-to-open special preparation.
- RadiusPreparation.lemma_4_3: approved at-most-one correction, all target radii.
- InverseDifferencePreparation.lemma_4_4: singleton inverse-difference RV range.
- BalancedHulls.observations and BalancedBallClasses: the 4.5 geometry.
- BalancedSlope.remark_4_6 and CompatibleFibreSlopes.ratio: actual slopes.
- Cells and ParameterizedCells: native geometric and definable predicates.
- OneCellDecomposition.exists_map: arbitrary mixed unary domains.
- TwoCellDecomposition.lemma_4_8: full actual original-base RV decomposition.

The final 4.8 construction runs through VerticalPresentation,
ScalarPositionDecomposition, PreparedBodyCells, PreparedRefinementFibres,
VerticalPullbackCells and the label-base definability modules. Its actual
GammaRVMap and all definable cell ingredients are constructed; it has no
cell/family/gluing existence input. Read the full types before reusing
intermediate conditional builders; the final theorem discharges them.
Native coordinate 1 is the first coordinate of the displayed pair fibre.

The final local audit passed 445 unique public theorems and function
constructions, including every complete exported type, with only propext,
Classical.choice and Quot.sound. Exact source and pin identities are in
`.scratch/section4-verified/receipt.json`; final published evidence is recorded
in VERIFICATION.json. Root build and full project integration checks passed for foundation and
Sections 2–5; Sections 6–7 have no verifiers. CI 43100323010 passed on proof commit 802eb9c. Artifact 13892318636
matches all complete types, axiom records, source/pin inputs and audit
hashes exactly. Publication adds only receipt/documentation changes to
those checked proof sources; see VERIFICATION.json.

The author-approved 4.3 correction is recorded in PAPER-CORRECTIONS.md.
OpenPolydiscBoundary checks the 4.7 singleton counterexample over any original
Gamma base. CellRectangles.rectangle proves the author's approved general
product statement. Its open-polydisc consequence with open first projection
is also proved. Definition 4.7 and Lemma 4.8 are unchanged.

The earlier ordinary least-radius existence claim was stale and withdrawn.
Upstream LeastLinearRadiusExistence proves ordinary existence and constructs
its function. The distinct whole-VF boundary has no least GammaTop radius.
Section 4 prepares the full uniformly definable radius/slope relation.

The integration base is CI-verified 53b98da; dependency pins are unchanged.
Activate Lean with `source /workspace/.tools/activate-lean.sh`. Dependencies
have built locally from source; do not repeat unavailable cache downloads.
No new outside citation, HK theorem or referee assertion is a proof input.
PROOF-WRITEUP.md records the completed replacement mathematical routes.
