# Section 5 targets

Source: [arXiv:0809.0473v2](https://arxiv.org/html/0809.0473v2#S5),
Section 5, Contracting to RV, through Corollary 5.8.
This is the sequel's numbering. The author's active category scope is RV[k],
the actual pinned finite-volume full subcategory. RV[k,*] is abandoned as a
target; existing ambient results are internal proof inputs.

Use the pinned LRV, the single absorbing RV element, actual mixed Point n m
sets, genuine saturation and the original real/Gamma parameter base. Auxiliary
RV arities are arbitrary. FiniteMixedRVFibres fixes all VF coordinates and
requires the remaining RV-label set to be finite. The producers derive finite
volume for the actual constructed contractions; they do not assume it as an
open conclusion. Internal real presentations are constructed and are not
subject to a new smallness premise.

| Item | Active target | Checked entry point |
| --- | --- | --- |
| 5.1 | For a Gamma-definable map between finite-RV-fibre mixed sources, construct two actual specials to RP targets with a contractible conjugate and both finite RV volume maps. | [lemma_5_1_finite](IntegrationSection5/FiniteGeometryPreparation.lean) |
| 5.2 | For a unary Gamma-definable bijection with finite source RV fibres, construct matched actual special preparations, mutual contractibility, the unique commuting key bijection, and an actual Gamma RV[1] iso. | [lemma_5_2_finite](IntegrationSection5/FiniteGeometryPreparation.lean) |
| 5.3 | On the actual prepared unary map, obtain the actual RV[1] iso, both full Gamma graphs and the key square, deriving target finiteness. | [lemma_5_3_finite](IntegrationSection5/FiniteNumbered.lean) |
| 5.4 | Actual coordinate-fibre maps and special witnesses, with the other VF coordinates as fibre parameters; exact factorization of actual special bijections. | special_relativeSpecial_factorization; finite Gamma-bijection closure in FiniteMixedRVFibres |
| 5.5 | For every finite arity and VF permutation, internally construct the standard program, actual RV[n] objects, first-n normalization, natural lift and global special presentation with VF-fixed Gamma charts. | [lemma_5_5](IntegrationSection5/FiniteStandardContractionData.lean), normalizedSpecialPresentation, gammaNormalizationIso |
| 5.6 | For positive VF arity p+1 and finite source RV fibres, construct a finite disjoint covering Gamma partition and actual relatively unary chains, including a common real realization and finite RV fibres at every intermediate stage. | [lemma_5_6_finite](IntegrationSection5/FiniteUnaryPartition.lean) |
| 5.7 | For every actual definable2-cell, construct both standard contractions and an actual Gamma RV[2] iso. Both finite volumes follow without an extra source hypothesis. | [lemma_5_7_finite](IntegrationSection5/FiniteNumbered.lean) |
| 5.8 | For a Gamma mixed VF2 source with finite RV fibres, construct a VF-fixed cell-label injection, both whole-source standard contractions and the actual Gamma RV[2] comparison. | [lemma_5_8_finite](IntegrationSection5/FiniteRVComparison.lean) |

All rows pass the 1852-head full type/allowed-axiom audit, manual review and
root 10708/full-project verification. See STATUS.md for evidence and assumptions.

## Precise 5.5 presentation

StandardSpecialPresentation carries an actual pinned SpecialBijection and its
complete Gamma chain, together with two Gamma isomorphism charts. Both charts
fix every VF coordinate and are RV-coordinate projections on their domains.
The square is the chosen actual natural lift. NormalizedStandardSpecialPresentation
retains the square for the pinned lift with the volume coordinates first.
This makes the paper's Notation 2.5 presentation convention explicit. A padded
chain target is not claimed to be an RP subset; its chart target is the actual
RV lift. The unchanged-arity natural map is not asserted to be a literal
pinned special bijection.

The coordinate-injectivity observation after Definition 5.5 is also checked.
The active scope retains the full original-Gamma graphs and genuine model,
characteristic, saturation, smallness and field-base assumptions in each type.
Only propext, Classical.choice and Quot.sound are permitted axioms.
