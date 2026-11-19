# hNames call-site map (read-only survey, November 18, 2026)

Paths are relative to `section 7/Integration7/` unless marked §6
(`section 6/IntegrationSection6/`). Counts are from grep; nothing was built.

## 1. Patterns of genuine use

- **P1. Gamma set → raw `DefSet S`.** `SetDefinable.mono _ (gamma_native_set_common_names h) hNames`
  in GammaSpecialCommonNames:17 (`gammaNativePresentation`), GammaRVLabelCuts:35 (`rvLabelCut`),
  NativePairPresentations:47, NativeRVParameterSelections:19, NativeCellFamilyPartitionDomains:21,
  UniformZeroParadigmContractions:22, MatchingPreparedFamilyDomains:44,
  PreparedDifferentRectangleFamilies:56, UnaryChainCommonNameRealization:29,34.
- **P2. Gamma graph → raw `Map A D` / `RelationDefinable … S`.** `gamma_native_graph_common_names`,
  `gamma_native_scalar_common_names`, `gamma_raw_rv_relation_common_names`: GammaMixedIsomorphismMaps:20,
  GammaRVGraphRefinements:70 (`gammaRVGraphRefinementMap`, feeding `gammaRVGraphRefinement`,
  GammaRVGraphRefinementGeometry:23, ~280 forwarding lines in 54 files), UnaryChainCommonNameRealization:38,
  UniformCellRefinementCentres:86, GammaRVCommonNameRebasing:17,33, TwoOrderProductCommonNameVolumes:67.
- **P3. Special chains / foci → raw `Chain S` / `SpecialBijection`.** `gammaChainPresentation`,
  `gammaSpecialPresentation` (GammaSpecialCommonNames:53,109); `gamma_unary_pullback_preparation_over_common_names`
  (11 calls in 8 files); `.present` in TwoOrderProductCommonNames:20, ConstantLabelPreparationCommonNames:20.
- **P4. `DefinableOverBase B` → `DefinableOver S` (balanced translation centres).**
  NativeBalancedTranslationCommonNames:33-34; inlined at RVParameterizedCellContractionComparisons:92,
  GammaNamedBalancedCellComparisons:51, DefinableCellContractionComparisons:79.
- **P5 (key). Volume objects/isos/blowups descended from `D.base` to `C.base`.**
  `GammaVolumeObjects.overCommonNames` (GammaVolumeCommonNameRebasing:17) → `gammaVolumeIsoOverCommonNames`,
  `elementaryBlowupOverCommonNames`, `volumeBlowupOverCommonNames`, `gamma_blowup_admissible_over_common_names`
  → `CommonContextVolumeEquivalent.descend` (CommonContextVolumeDescent:45). Consumers
  `(H.descend hc C hNames).toOrdinary`: PositiveVolumeLiftKernel:25, IntegrationCoordinateDensityFormula:42,
  FieldBaseUnaryRetainedContractions:50, FieldBaseUnaryIntegralBijections:48,
  SelectedRetainedContractionIntegrals:63, IntegrationStandardContractionFormula:85,
  FieldBaseUnaryVolumeIntegrals:79, SelectedFamilyIntegralComparison:31; and `hContext.descend` at
  NativeCoordinateVolumeFamilyRows:82, VolumeFamilyFormulaWitnessDescent:43. Each turns a
  `CommonContextVolumeEquivalent B C` into a raw `VolumeBlowupEquivalent` over C.base, i.e. into
  `PositiveVolumeBlowupClasses hc C k`.
- **P6. Context transport.** `frozen_head_volume_context_common_names` (FrozenHeadVolumeIntegrals:28, 17 uses),
  `vf_parameter_volume_context_contains_common_names` (NativeCoordinateVolumeFamilyRows:20),
  `frozen_generated_context_contains_names` (FrozenGeneratedVolumeContexts:53),
  `hNames (Or.inl …)` for `P.real ⊆ C.base` (UnaryPullbackCommonNamePreparations:27). These only feed P5.

## 2. Root lemmas

- GammaNativeCommonNames:146,151,170 (set/graph/scalar): no hNames; conclude definability over
  `commonRealNames B`. The base fact.
- GammaRVCommonNames:50 `gamma_raw_rv_relation_common_names (hNames : commonRealNames B ⊆ R)`.
- Generic `(hNames : commonRealNames G ⊆ S/T/R)`: GammaSpecialCommonNames:17,22,53,109; GammaRVLabelCuts:35;
  GammaRVGraphRefinements:70; NativePairPresentations:47; NativeRVParameterSelections:19;
  GammaMixedIsomorphismMaps:20; UnaryChainCommonNameRealization:20; NativeBalancedTranslationCommonNames:22;
  GammaRVCommonNameRebasing:17,33; GammaVolumeCommonNameRebasing:17; GammaBlowupCommonNameAdmissibility:15;
  GammaElementaryCommonNameRebasing:17,41.
- `C.base`-specific: GammaVolumeCommonNameIsomorphisms:18, GammaVolumeBlowupCommonNameRebasing:17,
  CommonContextVolumeDescent:16,31,45, UnaryPullbackCommonNamePreparations:21, ConstrainedUnarySources:17.
- Over `⟨C.base,Ξ⟩`: FrozenHeadVolumeIntegrals:28, NativeCoordinateVolumeFamilyRows:20,
  FrozenGeneratedVolumeContexts:53.

## 3. Category types

Raw over C.base: `RVVolumeObject` (HKRVVolumeObjects:19); `VFVolumeObject` (HKZeroVolumeIntegration:48,
VFVolumeObjects:25); `VFVolumeClasses`/`RVVolumeBlowupClasses` (HKZeroVolumeIntegration:56,60,
AllDegreeVolumeClasses:29); `PositiveVFVolumeIsoClasses` (VFVolumeClasses:49);
`PositiveVolumeBlowupClasses` (VolumeBlowupClasses:17, `muIspSetoid`); `ZeroVFVolumeClasses`
(HKZeroVFVolumeObjects:59).

Existing Gamma counterparts (raw over code set S + Gamma graphs): `VolumeObjectGamma`
(GammaVolumeObjectGraphs:20), `RVMapGamma` (GammaRVMapGraphOperations:21), `GammaVolumeObjects B S k` /
`GammaVolumeIsoClasses` (GammaVolumeIsomorphismClasses:16,27), `RVVolumeIso.GammaDefinable`
(GammaVolumeBlowupRowPromotion:21), `VolumeBlowup.GammaDefinable` (GammaChartedVolumeBlowups:19),
`GammaBlowupCenter`, `GammaIteratedVolumeBlowup`, `GammaVolumeBlowupEquivalent`,
`CommonContextVolumeEquivalent B C` (CommonContextVolumeEquivalences:15; witnesses in any D ⊇ C).
No quotient by `CommonContextVolumeEquivalent` and no Gamma VF class type exist in Section 7.

Code-set change: upward `GammaVolumeObjects.extend` (GammaVolumeParameterGeometry:35); downward
`overCommonNames`; names-containing contexts `gammaNamesContainingVolumeContext` (GammaNamesVolumeContexts:16),
`gammaDefinableNamesVolumeContext`, `gammaRVDefinableNamesVolumeContext`; definable-name elimination
`VolumeBlowupEquivalent.descend_definable` (DefinableVolumeParameterDescent:20). `GammaNamed*Comparisons`
already discharge hNames by moving to a names-containing context (e.g. GammaNamedRectangleComparisons:43).
Closed §6: `GammaObjectAt B S n` (FiniteGammaObjects:20), closed classes use S = Set.univ
(ContextRVClasses:18); `GammaObjectAt.changeBase` changes the Gamma base (RVClassBaseChange:18);
`gammaObjectAtExtend`; VF side uses code-free `GammaVFAllFiniteObject`.

## 4. Gamma-definability is carried through

Every root takes and re-exports Gamma-definability (`GammaSetDefinable`, `GammaGraphDefinable`, `RVMapGamma`,
`GammaChainDefinable`, `f.GammaDefinable`), often definitionally. It is discarded only by `.toOrdinary` in P5
(GammaIteratedVolumeBlowups:25, GammaVolumeBlowupEquivalence:40).

Main finding: P5 objects are already raw over C.base (e.g. `F.standardAppendObject` with
`volume_object_gamma_over_real_base`); only the equivalence witnesses live over a larger D. On the RV side,
removing hNames mostly means changing the class relation from raw `VolumeBlowupEquivalent` to
`CommonContextVolumeEquivalent B C`, not the objects. `lemma_7_5_positive_objects` has no hNames.
P1–P4 roots are generic in S and can be called with `S := (gammaNamesContainingVolumeContext …).base`.

Unclear: the VF side. Prop 7.8 (PositiveVolumeLiftKernel:17) matches the raw RV relation to raw VF isos; if
the RV relation becomes `CommonContextVolumeEquivalent`, VF iso classes probably need a matching
common-context/Gamma relation. Not checked whether `rv_volume_lift_coordinate_kernel` uses hNames genuinely.

## 5. Suggested order (bottom-up)

1. Keep P1–P4 roots (~20 files) and the volume rebasing layer (7 files).
2. New class types: blowup classes modulo `CommonContextVolumeEquivalent` (on `GammaVolumeObjects ⟨C.base,Ξ⟩ C.base k`
   or raw objects) and matching VF classes (~3–5 files, modelled on GammaVolumeIsomorphismClasses and
   VolumeBlowupClasses).
3. The 10 P5 consumers: drop descend/toOrdinary; remove hNames from `selected_family_*_integral_*`,
   `FieldBase*`/`Canonical*` integrals (~15 files).
4. The 17 `frozen_head_volume_context_common_names` users (~16 Frozen*/HKFrozen* files) and 2 `vf_parameter_*` users.
5. The Lemma 7.7 / two-order chain (~60 files forwarding `{hNames}`): discharge once at the top via
   `gammaNamesContainingVolumeContext` + `gamma_names_context_preserves_independence`, or leave generic;
   `lemma_7_7` already concludes `CommonContextVolumeEquivalent`.
6. HK aggregation/headlines (~300 forwarding files): mechanical deletion after 2–4.
