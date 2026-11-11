# Section 4 status

Work is on `section-4/translation-offsets`, updated to CI-verified upstream `53b98da`.
The user requested the whole section. All numbered lemmas and the balanced-cell observations now compile,
including the full definable-cell conclusion of 4.8. Full local integration
verification and source-matched CI passed.
Dependency pins are unchanged. All dependencies needed for the current
batch have now built locally from source.

## Established modules

- 4.1: `GammaOffsets.lemma_4_1` constructs the original-Gamma-base offset
  graph and the actual inverse-fibre translation identity, including zero.
  `FiniteOffsets.lemma_4_1` adds the finite-range remark under genuine
  saturation, infinite cardinal, and a small original real base.
- 4.2: `LinearPreparation.lemma_4_2` constructs an actual original-base
  special bijection to an RV pullback. Each actual inverse VF piece is
  Gamma-linear and open-to-open. It prepares the complete radius/slope
  relation and a checked finite open-to-open partition. No definable
  least-radius function is an assumption. Genuine saturation, ACVF00,
  VF/Gamma generation, small real base, and a named nontrivial Gamma
  value are explicit.
- Corrected 4.3: `RadiusPreparation.lemma_4_3` gives at most one source
  radius on each actual inverse piece. A single preparation works for
  every ordinary target radius. The actual whole-field source case is
  included. The author-approved correction and checked empty counterexample
  are recorded in PAPER-CORRECTIONS.md and RadiusBoundary.
- 4.4: `InverseDifferencePreparation.lemma_4_4` constructs preparation
  making the actual inverse-difference RV range a singleton. It uses
  actual translated RV fibres, an actual open-to-open positioning bijection,
  the original graph and the actual partial inverse. The target projection
  is an actual open ball. No definability of the individual fibre paradigm
  is assumed.
- 4.5/4.7: `BalancedFibres` and `Cells` define the actual fibre identities,
  balanced positioning and two-cells. Elementary degeneracy and graph
  consequences compile. These definitions do not assert cell existence.
- 4.6: `BalancedSlope.remark_4_6` proves the nondegenerate slope equals
  the paradigm-value ratio from the actual fibre identities and linearity.

## Uniform construction for 4.8

The following supporting constructions compile:

- RelativeBijection, VerticalMeanStep, RelativeRootReduction,
  RelativeObstaclePreparation and RelativeGammaPreparation construct
  uniform vertical preparation while fixing the complementary VF coordinates.
- VerticalOffsets and VerticalCharts construct a uniform positioning map
  and the actual translated vertical RV fibres over the original base.
- FullBaseFiniteBounds/Means/Codes and FiniteScalarFamilies/FiniteImageFamilies
  construct intrinsic finite RV refinements over the unchanged full base.
- LocalConstancyFibres, FamilyLocalConstancy and FamilyPositionRefinement
  give uniform constant-or-injective refinement of scalar positioning maps.
- FamilyOpenPartition, FamilyLinearRows, GammaFamilySyntax,
  FamilyPreparedLinearity and FamilyLinearPreparation prove 4.2 uniformly
  with pre-existing RV labels. FamilyInverseDifferences supplies the
  uniformly definable inverse-difference relation.
- LinearBallRadius.image_ball, TranslatedRVGeometry.ordinary_ball and
  LinearRVClasses.image_class give actual radius and entire RV-class image
  equalities. BalancedCompletion.of_constant_difference proves the full
  horizontal identity from the singleton inverse-difference conclusion.

## Decomposition theorem

TwoCellDecomposition.lemma_4_8 constructs an actual finite-arity GammaRVMap
on every original-base definable native VF² set. Every nonempty fibre is a
DefinableTwoCell over the original Gamma base together with its output RV
tuple. Its full positioning graph and both paradigms are proved definable.
No cell-existence, uniform-family existence, gluing, or least-function
hypothesis is an input. Standing cardinal/saturation, ACVF00, small original
real base, VF/Gamma generation and named nontrivial value assumptions remain
explicit in the exported type.

VerticalPresentation and ScalarPositionDecomposition construct the two
uniform stages. PreparedBodyCells proves all three positioning alternatives.
PreparedRefinementFibres and VerticalPullbackCells identify the actual map
fibres. RVLabelSlices, UniformPositionGraphs, FibreDefinability,
PositionRowDefinability and DefinableParadigms prove the full label-base
content, including every possible balanced first paradigm.

## Ancillary observations

BalancedHulls.observations proves actual minimal closed hulls, the two
paradigm radii, strict bounds inside both projection balls, and the omitted
positioning points. BalancedBallClasses proves the actual ball bijection,
fibre constancy and the two rectangle descriptions of internal symmetry.
RVClassGeometry proves centre-translation invariance and the ball-translation
identity, with no selected quotient code as an existence hypothesis.

ParameterizedCells records the parameterized definitions. The unary
observation preceding 4.8 is proved in OneCellDecomposition.exists_map,
including arbitrary old RV coordinates and output-label-base definability.

The unqualified nonbalanced open-polydisc sentence after 4.7 is false when
the first 1-cell is a point. OpenPolydiscBoundary constructs the actual
original-base definable cell {1} × rv⁻¹(rv(1)), positioning map 0, and proves
its paradigm nonzero, its positioning not balanced, and that it is not an
open polydisc. CellRectangles.rectangle proves the precise general product
of a 1-cell and an open ball. CellRectangles.open_polydisc proves the version
with open first projection. The author approved replacing “an open
polydisc” by “a product of a 1-cell and an open ball.” The corrected
observation is therefore already proved by CellRectangles.rectangle.
Both Section 4 wording corrections are resolved. Definition 4.7 and the
proved Lemma 4.8 are unchanged.

## Verification and publication

The final 445-declaration full-type/axiom audit passed. The full root build
passed (10,382 Lake jobs, mostly reused artifacts), and
`lake env python3 scripts/verify_ci.py` passed for foundation and Sections
2, 3, 4 and 5. Sections 6 and 7 have no verifiers and are skipped.
The earlier section-library build passed 9,921 Lake jobs.

VERIFICATION.json records every complete exported type, allowed axioms,
exact source/pin hashes and root/project integration evidence. Only propext,
Classical.choice and Quot.sound occur. Live logs are in
`.scratch/section4-verified/`, `.scratch/section4-root-final.log` and
`.scratch/section4-project-final.log`. [CI 43100323010](https://github.com/daviddhilbert/integration-in-ACVF/actions/runs/43100323010)
passed on proof commit 802eb9c (attempt 2; the initial attempt failed its
GitHub toolchain download before compiling Lean). Downloaded artifact
13892318636 matches all 445 complete types/axiom records, all 100 audited
source/pin inputs, compiler, dependencies and both audit hashes exactly.
The proof sources are promoted with only receipt/documentation updates
following that checked commit. No new proof source or pin change is part
of the publication record.

## Least-radius clarification

The latest upstream proves ordinary-source least-radius existence and an
ordinary least-radius function in LeastLinearRadiusExistence. An earlier
claim that ordinary existence was unresolved came from an outdated checkout
and has been withdrawn. The distinct whole-field boundary has no least
GammaTop radius. A threshold-function-definability conclusion is not claimed
by that upstream existence theorem. The 4.2 proof above uses the uniformly
definable radius/slope relation directly.
