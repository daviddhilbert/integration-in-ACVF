# Section 4 targets — 2-cells

Source: arXiv:0809.0473v2, Section 4, read in the arXiv HTML rendering.
There are five numbered lemmas: 4.1–4.4 and 4.8. Items 4.5 and 4.7
are definitions; 4.6 is a remark with downstream mathematical content.

## Standing assumptions

Return to the original structure C, rather than Section 3's ball-name
expansion. The paper assumes pure characteristic zero, genuine sufficient
saturation, a small VF/Gamma-generated parameter substructure S, and a
nontrivial Gamma(S). Keep any assumptions actually needed in exported types.
The elementary real-base 4.1 proof should need only ACVF and an arbitrary
real parameter set. Its Gamma-base graph descent must be proved separately.

Use the pinned corrected LRV language, its existing VF field and single
absorbing RV element. The paper's infinity is the existing RV zero. Equal
valuation is weaker than equal RV class. Mathlib's multiplicative valuation
order reverses the paper's order. Do not introduce a fresh RV model.

## Target inventory

| Item | Intended content | Prerequisites and status |
| --- | --- | --- |
| 4.1 | For an actual unary special bijection onto an RV-pullback, construct an original-base definable offset on the final RV-label image; its inverse fibres are translates of their actual RV fibres. Include the absorbing fibre. | Completed by FiniteOffsets.lemma_4_1, including original-Gamma-base graph descent, finite range, and the absorbing fibre. |
| 4.2 | Prepare a definable unary bijection by an actual special bijection whose inverse RV pieces are Gamma-linear and open-to-open. | Completed by LinearPreparation.lemma_4_2. The full radius/slope relation is prepared; no definable least-function input is assumed. |
| 4.3 | Prepare constant source radii for subballs with prescribed image radius. | Completed by RadiusPreparation.lemma_4_3 with the author-approved “has at most one element” correction. One preparation works for all ordinary target radii, including whole-VF source candidates. |
| 4.4 | Prepare the inverse-difference RV class for translated fibres and an open-to-open positioning bijection. | Completed by InverseDifferencePreparation.lemma_4_4; FamilyInverseDifferences retains all free context labels. |
| 4.5 | Balanced positioning, both fibre identities and the subsequent geometric observations. | Cells and BalancedFibres give the definitions. BalancedHulls proves actual minimal hulls, omitted centres and strict radius bounds. BalancedBallClasses proves the ball bijection, fibre constancy and both internal rectangle unions; RVClassGeometry proves the translation identities. |
| 4.6 | Paradigm-value slope ratio and compatible special-fibre slope ratio. | Completed by BalancedSlope.remark_4_6 and CompatibleFibreSlopes.ratio, explicitly in the nonzero/ordinary scope where the ratios belong to Gamma. |
| 4.7 | One-cell, two-cell, parameterized and definable predicates, and their graph/rectangle consequences. | Cells and ParameterizedCells give the definitions. Graph-of-zero is proved. CellRectangles proves the precise nonbalanced rectangle shape and the open-polydisc version with open first projection. OpenPolydiscBoundary independently refutes the unqualified open-polydisc sentence. The author-approved replacement, “a product of a 1-cell and an open ball,” is proved by CellRectangles.rectangle. |
| Before 4.8 | A definable VF × RV^m set admits an RV map with one-cell fibres. | OneCellDecomposition.exists_map constructs the actual original-base map, preserves the old labels, and proves full label-base definability. |
| 4.8 | Every original-base definable VF² set has a finite-arity original-base RV map whose nonempty fibres are definable two-cells. | Completed by TwoCellDecomposition.lemma_4_8, including actual positioning graphs and both paradigms over the output label base. No cell/family/gluing existence hypothesis remains. |

## Dependency classification

Checked source imports to be rebuilt locally: predecessor's actual
`SpecialBijection`, `Chain.unary_sub`, `inverse_contractible`, full real-base
map graphs and image constructions. Section 3's published 3.19 is available
with explicit cardinal, genuine saturation, ACVF00 and named nontrivial
Gamma assumptions. Latest upstream 3c3e478 additionally proves ordinary-source least-radius
existence and provides the uniformly definable radius/slope row. The older
conditional export still includes VF; the whole-field boundary has no least
GammaTop radius. A separate threshold-function-definability conclusion is
not asserted by the upstream existence theorem.

No Section 4 lemma, cell-decomposition conclusion, HK result, referee claim,
or new outside citation is accepted as a proof input. The author approved the at-most-one correction to 4.3; see
PAPER-CORRECTIONS.md.
