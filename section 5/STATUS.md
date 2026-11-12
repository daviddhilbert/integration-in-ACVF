# Section 5 status

The active Section 5 targets are complete in the author's RV[k] scope. RV[k]
means the pinned full subcategory of objects with finite-to-one volume maps.
Auxiliary RV arities are arbitrary. The finite-source condition is
FiniteMixedRVFibres: fixing all VF coordinates leaves finitely many RV labels.
The former ambient category is retained only as internal proof support.

Definition 5.5 is formalized with explicit original-Gamma RV presentation charts,
as described below. All other numbered results retain their recorded statements
and standing assumptions, restricted to finite RV fibres where applicable.

## Active entry points

| Item | Entry point | Constructed result |
| --- | --- | --- |
| 5.1 | [lemma_5_1_finite](IntegrationSection5/FiniteGeometryPreparation.lean) | Two actual Gamma special bijections to RV-pullbacks, a contractible conjugate with its full Gamma graph, and finite volume maps for both prepared objects. |
| 5.2 | [lemma_5_2_finite](IntegrationSection5/FiniteGeometryPreparation.lean) | Both actual special preparations, mutual contractibility, the unique commuting key bijection, and an actual RV[1] isomorphism with both Gamma graphs. Target finiteness follows from source finiteness. |
| 5.3 | [lemma_5_3_finite](IntegrationSection5/FiniteNumbered.lean) | The actual finite-category isomorphism and induced-key square for the prepared mutually contractible unary bijection. |
| 5.4 | [special_relativeSpecial_factorization](IntegrationSection5/RelativeSpecialFactorization.lean) | Actual coordinate-fibre special witnesses and exact relatively-special factorization. Complementary VF coordinates are the added fibre parameters. Finite RV fibres are preserved by Gamma bijections. |
| 5.5 | [lemma_5_5](IntegrationSection5/FiniteStandardContractionData.lean) | Internally presented standard contraction for every VF order, native and normalized RV[n] objects, natural Gamma lift isomorphism, and actual global special presentation. |
| 5.6 | [lemma_5_6_finite](IntegrationSection5/FiniteUnaryPartition.lean) | A finite disjoint covering Gamma partition, actual relatively unary factors, a common real realization, and finite RV fibres at every intermediate factor. |
| 5.7 | [lemma_5_7_finite](IntegrationSection5/FiniteNumbered.lean) | Both actual standard contractions and an actual Gamma RV[2] isomorphism for every definable 2-cell. Finite volume is derived without an additional source hypothesis. |
| 5.8 | [lemma_5_8_finite](IntegrationSection5/FiniteRVComparison.lean) | A VF-fixed positioned cell-label injection and both whole-source standard contractions, with an actual Gamma RV[2] comparison and both finite volume maps. |

The files live in IntegrationSection5. The declaration namespace is
IntegrationInACVF.Section5; the links identify their source modules.
GammaRVFiniteIso stores an isomorphism in the actual RVFiniteObject category
and the complete original-Gamma graphs of its hom and inverse.

## The explicit presentation in 5.5

The paper identifies definably bijective presentations in Notation 2.5 and calls
the natural map before Definition 5.5 special. StandardSpecialPresentation makes
the changes of RV presentation explicit: an actual pinned SpecialBijection,
its complete Gamma chain certificate, two Gamma isomorphism charts, and a
commuting square with the chosen natural lift. Both charts preserve all VF
coordinates and are given by RV coordinate projections on their domains.

FiniteStandardContractionData.normalizedSpecialPresentation additionally gives
the chart onto the actual pinned normalized lift, with volume coordinates
first, and its exact square with normalizedNaturalLiftMap. This does not assert
that the padded special-chain target itself is an RV-pullback; its chart target
is the actual RV lift. No literal unchanged-RV-arity special witness is claimed.

The finite compiler constructs activity flags internally from the actual finite
preparation trace. Each weak focus becomes a genuine global focus on the flag
locus intersected with the current RV hull. Full canonical steps and empty
foci enforce alternation. Actual projection squares and bijections give the
charts. Original-Gamma certificates are retained through restriction, parameter
extension, coordinate lifting and permutations. No uniform trace, comparison,
finite image, flag certificate or preparation conclusion is a premise of the
numbered producers.

FiniteStandardContractionData.gammaNormalizationIso is an actual Gamma RV[n]
isomorphism from the selected-volume object to its first-n normalization.
FiniteStandardContractionData.naturalLiftIso gives the normalized Gamma lift.

## Hypotheses

All declarations use the pinned LRV and its single absorbing RV element.
The finite producers retain genuine saturation, aleph0<=kappa and small
original G.real. Preparation results use ACVF00 and VFFieldBase G.real where
shown in their full types. Lemmas 5.2, 5.7, 5.8 retain a named Gamma value delta>1;
5.8 also retains VFGammaGeneratedBase G. The presented 5.3 statement needs only
the checked prepared-map hypotheses and the recorded saturation/smallness.

Lemma 5.6 has positive VF arity p+1 and requires a Gamma value delta>1; its actual
full type does not require delta membership in G.gamma or VFFieldBase. The
zero-VF case is outside that relatively-unary statement. Lemma 5.5 covers all
finite arities, including zero. No theorem assumes that an internally enlarged
real code set is small.

## Verification

1852 complete headline types and allowed-axiom audits PASS. All 1686 prior full
types and axiom records are exact. All 166 additions, including structure and
inductive constructor interfaces, were manually reviewed in 1997 readable lines.
Root build: 10708 jobs. The whole-project verifier passes foundation and
Sections 2, 3, 4, 5; Sections 6, 7 have no verifiers and are skipped.

Evidence is retained in .scratch/section5-final-1852-verified/. VERIFICATION.json is
the compact source/pin/type-hash/axiom index; VERIFICATION.json.gz retains the
complete unmodified raw receipt losslessly. Only propext, Classical.choice and
Quot.sound are allowed. Dependency pins and the Lean toolchain are unchanged.

The prior 1686 checkpoint is ceb309c9e2e98fadd6fdc10252b0d99590a2febe.
Publication and CI for this 1852 proof revision are checked after local
verification; exact artifact comparisons are recorded in .scratch/.
This session promoted only the explicitly approved 30071af checkpoint. Remote main
has since advanced separately to 0055851; that work is preserved. No additional
main promotion is authorized here.
