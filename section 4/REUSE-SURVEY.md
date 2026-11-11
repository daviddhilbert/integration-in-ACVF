# Section 4 reuse survey

## Source identity and policy

Initial published project base: c8f4270. Updated to verified upstream
3c3e478 after the section 1-3 chat completed its newer work, then
fast-forwarded to CI-verified 53b98da for integration with Section 5.
Lean: leanprover/lean4:v4.35.0. Pins are unchanged:

- Special transformations: 9cc9760892092dd34cfad4a6dee655843c52f30c.
- ACVF-QE: 939346b0a99899e22a873479364e3cc5d142731c.
- Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679.

Read the predecessor's LANGUAGE-ERRATA.md and Section5/STATUS.md before
reuse. The named RV inverse, the leading-term linkage, the absorbing element,
and original-base full-graph conventions are retained. Historical standalone
Section5/Sec5.lean and LegacyScaffold are not the actual imported framework.

Follow the section 1-3 chat and repository workflow: compile and audit locally
before pushing; CI confirms integration. HK is only a possible source of
ideas, never a cited or assumed unproved input. Maintain PROOF-WRITEUP.md
when a completed proof differs substantially from the paper's proof.

## Lemma 4.1

Reuse `SpecialTransformations.Section5.SpecialBijection` from
Section5/Core.lean. It stores an actual finite chain with genuine alternation,
not a predicate asserting special-bijection existence. `inverseMap` is an
actual same-base definable map with `inverse_apply` and `apply_inverse`.

Section5/TransformGeometry.lean proves `Chain.unary_sub`: equal final RV
labels imply preservation of VF differences. Its hypotheses include ACVF,
an arbitrary real parameter set and finite tuple arities; there is no extra
characteristic, saturation or nonzero-fibre assumption. This supplies the
geometric induction already needed by 4.1. `inverse_contractible` retains
all original RV classes and labels. `unary_inverse_fibre` identifies ordinary
nonzero inverse balls, but its nonzero hypothesis makes it insufficient by
itself for the complete 4.1 statement.

Section4/DefinableGeometry.lean, Products.lean and CodeMaps.lean supply
the presented spaces, actual maps with full graphs, composition, products,
images and coordinate projections. The new `DefinableDescent` module
factors a fibre-constant definable map through the actual image of a
definable map. It uses internal representative choice and proves graph
definability by existential composition. The representatives are never
added to S. `TranslationOffsets` applies this to the inverse displacement.

The generic descent and translation proofs use imported declarations.
The later relative vertical preparation adapts the checked geometric
arguments of the pinned predecessor's VerticalConstruction, Centering and
root-reduction modules, with attribution in RelativeSlices and
RelativeObstaclePreparation. Its relative maps retain the complementary
VF coordinates, which the general special-bijection interface does not
record. No dependency files or pins are modified. No root license file was
found in the predecessor checkout; no license claim is made for that source.
Pinned Mathlib identifies its Apache-2.0 license. No additional external
source or unproved external result is introduced.

The dependency source builds and root build completed locally. The current
Section 4 verifier supersedes the initial descent-only receipt; it builds
Library and audits every exported theorem and the actual descent/offset
map constructors. The earlier all-module batch passed 137 complete-type
and permitted-axiom checks. Consult the current exact source hashes and
final status in `.scratch/section4-verified/receipt.json`.

## Wider survey

Searched this project's Section 3 for native ball, radius, Gamma-linearity,
open-to-open and parameter-base definitions. Reuse its actual ball predicates
and its published theorem signatures rather than duplicating them.
The initial checkout recorded a least-radius existence followup. That note
was stale: latest main 3c3e478 proves ordinary-source existence in
LeastLinearRadiusExistence.ordinary_function and supplies the uniform
GammaLinearBallRow.row_definable relation. The current handoff preserves
the separate VF boundary, where no least GammaTop radius exists. Use the
new checked declarations; do not repeat the stale ordinary-existence claim.

Searched ACVF-QE's Proofs and pinned Mathlib's ModelTheory sources for
balanced cells/bicells/two-cells: no usable implementation found. External
GitHub searches for `SpecialBijection unary_sub` and ACVF two-cells found no
additional usable Lean project; the Mathlib balanced-cell search returned
unrelated algebra/topology results. These are limited discovery results,
not a claim that no such formalization exists. No external result was
adopted. Continue surveying before rebuilding substantial new prerequisites.

For the 4.3 boundary check, the existing actual-ball theorem
`BallEnlargementGeometry.gamma_radius_le_of_subset` is relevant. It derives
the paper-order radius inequality from inclusion of actual ordinary balls,
with a nontrivial Gamma value explicit. No assumed radius-monotonicity or
outside geometric input is required.

## Uniform families and balanced completion

The finite-family route reuses the checked predecessor Barycentre.code
separation theorem (RawBarycentricCode), FullFibreMeans, the real
uniform_finite_fibre_bound compactness theorem, and the full interpreted
parameter-base logic from Section 3. FullBaseFiniteCodes supplies all full
original-base graphs of the intrinsic means and recursive RV codes.
FiniteScalarFamilies and FiniteImageFamilies keep context labels free.

LocalConstancyFibres uses the checked VF exchange theorem and
FiniteFibresFromExchange to prove finite image on the locally constant
locus, and actual finite polynomial obstacles to prove finite fibres off
that locus. FamilyLocalConstancy specializes finite contexts only inside
these proofs; FamilyPositionRefinement exports unchanged-base RV graphs.

FamilyOpenPartition reuses SingleCoordinatePartition.full_base for the
actual tuple map preserving all context coordinates. FamilyLinearRows
carries those free coordinates through GammaLinearBallRow's quantified
radius/slope construction. FamilyPreparedLinearity and
FamilyLinearPreparation use actual inverse pieces and genuine special
bijections. None assumes a definable least-radius function.

LinearBallRadius, TranslatedRVGeometry and LinearRVClasses prove actual
image-radius and entire RV-class image equalities. BalancedCompletion
uses them to obtain the reverse horizontal containment in Definition 4.5.
These are new checked arguments over the existing native carriers; they
are not a cell-decomposition existence input.


## Balanced observations and unary decomposition

RVClassGeometry reuses the checked native RV closeness criterion and
FiniteClosedHull.open_hull_subset; valuation density proves minimality.
BalancedHulls connects both signed fibre identities to these actual hulls.
BalancedBallClasses uses LinearBallRadius.image_ball and the proved slope
ratio for the actual ball bijection and two rectangle unions. No additional
outside result or quotient-code choice is used. CellRectangles derives its
rectangle from the three actual positioning alternatives, not from the
printed unqualified observation. OpenPolydiscBoundary independently checks
the singleton first-projection boundary against the native definition.

OneCellDecomposition uses GammaDomainPreparation, actual inverse special
fibres, and RVLabelSlices to obtain the unary observation with all old RV
coordinates preserved. ParameterizedCells records the existing definition
fibrewise on the same native carriers. All these modules enter the final
complete-type and allowed-axiom audit.
