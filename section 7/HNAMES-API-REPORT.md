# Public-API change report: removing `hNames` (for diamond-integral)

Date: November 20, 2026. Branches (local, not pushed):
integration-in-ACVF `remove-hnames` and special-transformations `gamma-lift-9-16`.

## Summary

- **Additive only.** No existing declaration was removed, renamed or restated. Every
  registered source module of integration-in-ACVF hashes exactly as in `VERIFICATION.json`
  (0 changed). The corrected `HK` theorems still take `hNames`. diamond-integral keeps
  compiling against them unchanged, once the provider pin below is bumped.
- **New Gamma-named class API.** It covers 7.6–7.10 and 7.13 over `⟨C.base, Ξ⟩` with no
  `hNames`. The entry point is `Integration7.GammaNamedSection7Results`, which is imported by
  `Integration7.Library`.
- **New Gamma-named function layer (additive).** Entry point
  `Integration7.GammaFunSection7AdditiveResults`, also imported by `Integration7.Library`.
  - Gamma-named 7.11 and 7.12 hold in additive form: as equalities of additive monoid
    homomorphisms into `HK.GammaNamedRVSemiring`, and pointwise on each function.
  - Gamma-named 7.14 and 7.15 hold for homogeneous functions.
  - Both cover positive degree and weighted degree zero.
- **Linear layer: complete for the requested targets** on branch `gamma-linear-section7` (local,
  from `origin/main` 5a69a5e; the author asked for it). Entry points
  `Integration7.GammaFunLinearResults` (module and integral) and `Integration7.GammaFunLinearSection7`
  (7.11, 7.12, normalized 7.14, normalized 7.15), both imported by `Integration7.Library`.
  - Done: the graded Gamma-named functions (weighted degree zero in component zero, positive
    coefficient degree `k` in component `k+1`) form a module over `HK.GammaNamedRVSemiring`
    (`GammaFun.aeGradedAction`, instance `GammaFun.gradedAEFunctionModule`). The graded
    Gamma-named integral is `HK.GammaNamedRVSemiring`-linear (`GammaFun.gradedIntegralLinearMap`;
    `GammaFun.comp_integral_act` for every pair of degrees).
  - Done: **linear 7.12.** Jacobian transforms commute with coefficients of every degree on
    functions of every degree (almost everywhere). Supported graded functions form a module
    (`GammaFun.supportedGradedFunctionModule`), the Jacobian transform is linear
    (`GammaFun.suppJacLinearMap`), and `GammaFun.gamma_named_linear_proposition_7_12` is an
    equality of `HK.GammaNamedRVSemiring`-linear maps.
  - Done: **normalized 7.15.** The Gamma-named degree-one point class is central
    (`HK.gamma_point_class_commutes`). Localizing at it and normalizing homogeneous terms gives
    `HK.NormalizedGammaRVRing` with `HK.normalizedGammaCoefficientMap` (point ↦ 1). Normalized
    supported functions are the scalar extension of the supported graded module
    (`GammaFun.NormalizedSupportedFunction`); `GammaFun.gamma_named_normalized_linear_theorem_7_15`
    and `GammaFun.gamma_named_normalized_theorem_7_15` follow from linear 7.12.
    - Formulation (accepted by the author, November 19, 2026): the raw `HK.theorem_7_15` uses the span of supported
      generators inside the scalar extension of the full module, with a restricted Jacobian
      built from positive operators. The Gamma statement uses the scalar extension of the
      supported module itself. The two agree on generators; the carriers are not identified, and
      that identification is not a target.
  - Done: **head-integral coefficient linearity**, almost everywhere, in all four degree cases:
    `GammaFun.presentation_head_left_product_ae` (positive coefficient, positive function),
    `GammaFun.presentation_head_zero_coef_ae` (weighted degree-zero coefficient, positive
    function), `GammaFun.presentation_head_pos_zero_ae` (positive coefficient, degree-zero
    function), `GammaFun.presentation_head_zero_zero_ae` (both degree zero). Head rows are unary
    fibre-family contractions (`head_fibre_integral_volume_iso_gamma`); the coefficient product
    is contracted through a Gamma native coefficient preparation over the VF field base of the
    row (`gamma_field_unary_special_preparation`), and the two contractions are compared by Gamma
    Lemma 7.5 (rows at every point) or, in the degree-zero cases, at generic points through
    frozen generated contexts and `GammaFun.presentation_ae_of_generic_rows`.
  - Done: **linear 7.11.** The graded head integral is linear (`GammaFun.gradedHeadLinearMap`,
    `GammaFun.graded_head_fubini`); graded functions supported in `VF^(n+1)` are all graded
    functions (`GammaFun.gradedUnivEquiv`), so coordinate permutations are linear Jacobian
    transforms (`GammaFun.gradedPermuteLinearMap`); prefix integrals iterate head integrals
    (`GammaFun.gradedPrefixLinearMap`). The graded coordinate integral
    `GammaFun.gradedCoordinateIntegralLinearMap` agrees with `aeCoordinateIntegral` and
    `aeZeroCoordinateIntegral` on components (`GammaFun.graded_coordinate_integral_of`,
    `GammaFun.graded_coordinate_integral_of_zero`), and
    `GammaFun.gamma_named_linear_proposition_7_11` and `GammaFun.gamma_named_linear_theorem_7_14`
    are equalities of `HK.GammaNamedRVSemiring`-linear maps.
  - Done: **normalized 7.14.** `GammaFun.normalizedCoordinateIntegral` is the scalar extension of
    the graded coordinate integral; `GammaFun.gamma_named_normalized_linear_fubini`,
    `GammaFun.gamma_named_normalized_linear_theorem_7_14` and
    `GammaFun.gamma_named_normalized_theorem_7_14` follow from linear 7.11.
    - Formulation (author decision, relayed November 19, 2026): linear 7.11 and normalized 7.14
      are stated on all graded (resp. normalized) Gamma-named functions on `VF^(n+1)`, without a
      support set, and this unsupported formulation is retained. Asked whether to prove that
      Gamma-named coordinate integrals preserve supports (map functions on `X` to functions on
      the coordinate image of `X`), the author answered "Not needed". The raw `HK.theorem_7_14`
      is stated on normalized functions supported in `X`, with the coordinate image of `X` as
      target; integrals of supported functions are integrals of their underlying functions, so
      the identities carry the same content. Support preservation is not a target.
  - The corresponding `HK` statements still carry `hNames`.

## Dependency changes required

1. **special-transformations.** Bump the pin from `423c767` to `gamma-lift-9-16` @ `932a507`.
   - It adds eight additive commits (`e8ce0ad..932a507`) with 18 audited Section 9 headlines,
     including `Section9.GammaLift.gamma_theorem_9_16_finite_volume`.
   - The range also contains three provider commits that predate this work: `2d5f80e`,
     `0db959b` and `183d10d`.
   - Done: `lakefile.toml`, `lake-manifest.json` and `section 7/VERIFICATION.json` pin `932a507`
     (published on special-transformations main).
2. **integration-in-ACVF.** Bump diamond-integral's pin to the `remove-hnames` tip once it is
   published. The tip includes 81 new modules (49 class-level, 32 function-layer),
   `Library.lean` and documentation.
3. **Registry.** `section 7/VERIFICATION.json` registers the new modules and 132 declarations
   under `gamma_named_hnames_removal` (45 class-level; 87 in its `function_layer` entry).
   - `dependency_pins` names `932a507`, matching the manifest.
   - The blueprint has seven new nodes: `s7-gn-7`, `s7-gn-9`, `s7-gn-10`, `s7-gn-13`,
     `s7-gn-11`, `s7-gn-12` and `s7-gn-14`.
   - Its fingerprint manifest is already stale on `main` (46 drifted files in Sections 2–3), so
     it needs regeneration at publication.

## New public declarations (namespace `IntegrationInACVF.Section7`)

Categories and contexts:

- `gammaNamedBase C Ξ := ⟨C.base, Ξ⟩` and `gammaNamedCodeContext C Ξ hΞ`.
  - The code context is the substructure generated by `C.base` and the common names.
  - `gamma_named_code_context_names` and `gamma_named_code_context_generic` are the discharged
    obligations.
- `HK.GammaRVObjects B S n`: all-degree RV volume objects over `S` with Gamma domain,
  coordinates and density (`HK.RVVolumeObject.Gamma`).
- `HK.GammaNamedRVClasses hc C Ξ hΞ n`.
  - Degree 0: Gamma weighted objects modulo Gamma isomorphisms.
  - Degree k+1: Gamma blowup classes.
- `HK.GammaNamedVFClasses` (Gamma isomorphism classes) and `HK.GammaNamedRVIsoClasses`.
- `HK.gammaNamedRVClass`, `HK.gammaNamedVFLiftClass` and `HK.gammaNamedLiftOnClasses`.

Results (all with `hc`, `C`, `Ξ`, `hΞ`; where needed also
`hGenerated : VFGammaGeneratedBase ⟨C.base, Ξ⟩`, `γ ∈ Ξ` and `1 < γ`):

| Paper | Declaration |
| --- | --- |
| 7.6 | `GammaNamed.gamma_named_corollary_7_6` |
| 7.7 | `GammaNamed.gamma_named_lemma_7_7` (arbitrary contraction orders; Gamma contraction programs) |
| 7.8 | `HK.gamma_named_proposition_7_8` (all degrees), `gamma_named_blowup_class_eq_of_lift_class_eq`, `gamma_named_lift_class_eq_of_blowup_class_eq` |
| 7.9 | `HK.gamma_named_lift_on_classes_bijective`, `HK.gammaNamedIntegrationEquiv`, `HK.gammaNamedIntegrationAddEquiv` |
| 7.10 | `HK.gammaNamedRVClassesGSemiring`, `HK.GammaNamedRVSemiring`, `HK.gammaNamedGradedIntegrationEquiv`, `HK.gamma_named_theorem_7_10`, `HK.gammaNamedIntegrationRingEquiv` |
| 7.13 | `HK.gammaNamedGradedBlowupProjection`, `HK.gammaNamedBasicVolumeRelationIdeal`, `HK.gamma_named_raw_volume_kernel_principal`, `HK.gamma_named_theorem_7_13` |

Supporting public lemmas that diamond-integral may reuse:

- Gamma VF lifts of Gamma RV isomorphisms: `GammaNamed.rv_volume_iso_lift_gamma`.
- Product congruences: `GammaVolumeBlowupEquivalent.product_left`, `.product_right`,
  `.weightedZero`, `.weightedPositiveZero` and `HK.gamma_named_product_congr`.
- The Gamma basic relation: `gamma_degree_one_basic_volume_relation`.
- The transport input: `gamma_volume_transport_input`.

## New public declarations: Gamma-named function layer (namespace `IntegrationInACVF.Section7.GammaFun`)

Functions and operations (all with `hc`, `C`, `Ξ`, `hΞ`; integrals and integral operators also
take `hGenerated`, `γ`, `hγ`, `hγ1`):

- Presentations and quotients: `Presentation`, `AEEquivalent`, `AEFunction`,
  `ZeroPresentation`, `ZeroAEEquivalent`, `AEZeroFunction`.
- Gamma VF sets and bijections: `GammaVFSet`, `GammaVFBijection`.
- Supported functions: `SupportedAEFunction`, `SupportedAEZeroFunction`.
- Integrals: `aeIntegral`, `aeAppendedIntegral`, `aeZeroIntegral`, `gammaSemiringIntegral`,
  `gammaSemiringZeroIntegral`.
- Operators: `aeHeadIntegral`, `aeZeroHeadIntegral`, `aePrefixIntegral`,
  `aeZeroPrefixIntegral`, `aePermute`, `aeZeroPermute`, `aeCoordinateIntegral`,
  `aeZeroCoordinateIntegral`, `supportedJacobian`, `supportedZeroJacobian`.
- Additive structure: the `AddCommMonoid` instances `aeFunctionAddCommMonoid`,
  `aeZeroFunctionAddCommMonoid`, `supportedAEFunctionAddCommMonoid` and
  `supportedAEZeroFunctionAddCommMonoid`.
- Additive monoid homomorphisms: `aeIntegralAddHom`, `aeAppendedIntegralAddHom`,
  `gammaSemiringIntegralAddHom`, `aeZeroIntegralAddHom`, `gammaSemiringZeroIntegralAddHom`,
  `aeHeadIntegralAddHom`, `aeZeroHeadIntegralAddHom`, `supportedJacobianAddHom`,
  `supportedZeroJacobianAddHom`, `aePermuteAddHom`, `aeZeroPermuteAddHom`,
  `aePrefixIntegralAddHom`, `aeZeroPrefixIntegralAddHom`, `aeCoordinateIntegralAddHom`,
  `aeZeroCoordinateIntegralAddHom`.

| Paper | Declaration |
| --- | --- |
| 7.5 | `presentation_integral_eq_of_rows` (Gamma Lemma 7.5 on integrals) |
| 7.11 | `gamma_named_proposition_7_11` (any `VFCoordinateProjection`), `_7_11_zero` (at least one discarded coordinate), `_7_11_zero_permute`, `gamma_named_proposition_7_11_add_hom`, `_7_11_zero_add_hom` |
| 7.12 | `gamma_named_proposition_7_12`, `_7_12_zero`, `gamma_named_proposition_7_12_add_hom`, `_7_12_zero_add_hom` |
| 7.14 | `gamma_named_theorem_7_14` (nonempty retained sets), `gamma_named_theorem_7_14_zero`, `gamma_named_two_projection_fubini` |
| 7.15 | `gamma_named_theorem_7_15`, `gamma_named_theorem_7_15_zero` |

Supporting results: `ae_head_fubini`, `ae_zero_head_fubini`, `ae_prefix_fubini`,
`ae_coordinate_fubini`, `ae_zero_coordinate_fubini`, the AE-descent theorems
`presentation_head_integral_ae`, `presentation_jacobian_ae` and their zero versions, and the
additivity theorems `presentation_integral_add`, `presentation_head_integral_add`,
`presentation_jacobian_add` and their zero versions. The generic Gamma tools are
`GammaNamed.gamma_lift_contraction_comparison`, `GammaNamed.gamma_vf_iso_contraction_comparison`,
`GammaNamed.gamma_coprod_contraction`, `GammaBaseDominated` and
`GammaVolumeBlowupEquivalent.changeBase`.

## New public declarations: Gamma-named linear layer (namespace `IntegrationInACVF.Section7.GammaFun` unless noted)

Status: complete for the requested targets (see the summary). 146 headline declarations,
audited in `verification/hnames-removal/LinearLayerAudit.log`.

- Coefficient actions on presentations: `Presentation.leftProduct` (positive on positive),
  `Presentation.zeroCoef` (weighted degree zero on positive), `ZeroPresentation.posCoef`,
  `ZeroPresentation.zeroCoef`; uniformly `presAct`, with rows `pres_act_row`.
- Almost-everywhere actions and module: `AEComp`, `aeAct`, `aeAct_mk`, `aeActBiadditive`,
  `aeAct_one`, `aeAct_assoc`, `aeGradedAction`, `GradedAEFunction`, `gradedAEFunctionModule`,
  `graded_ae_action_of`.
- Integral linearity: `presentation_left_product_appended_integral`,
  `gamma_semiring_integral_positive_coefficient`, `presentation_zero_coef_integral`,
  `presentation_zero_coef_appended_integral`, `zero_presentation_pos_coef_appended_integral`,
  `zero_presentation_zero_coef_integral`, `comp_integral_act`, `compIntegral`,
  `gradedIntegralAddHom`, `graded_integral_smul`, `gradedIntegralLinearMap`.
- Jacobian linearity: `is_jacobian_value_map_comp` (namespace `Section7`),
  `Presentation.jacobianWith`, `ZeroPresentation.jacobianWith`, `presentation_jacobian_with_ae`,
  `zero_presentation_jacobian_with_ae`, `zero_class_eq_of_select` (namespace `Section7`),
  `presentation_left_product_jacobian`, `presentation_zero_coef_jacobian`,
  `zero_presentation_pos_coef_jacobian`, `zero_presentation_zero_coef_jacobian`.
- Supported module and linear 7.12: `PresSupported`, `pres_act_supported`, `SuppComp`,
  `suppForget`, `suppAct`, `suppGradedAction`, `SupportedGradedFunction`,
  `supportedGradedFunctionModule`, `supported_graded_action_of`, `presJac`, `suppJac`,
  `supp_jac_act`, `suppForgetLinearMap`, `suppJacLinearMap`, `suppIntegralLinearMap`,
  `gamma_named_linear_proposition_7_12`.
- Normalized coefficients (namespace `Section7.HK` unless noted): `gammaPointClass`,
  `gamma_point_class_commutes`, `GammaPointLocalization`, `normalizedGammaSemiringMap`,
  `NormalizedGammaRVRing`, `normalizedGammaCoefficientMap`, `normalized_gamma_coefficient_point`,
  `Section7.gamma_volume_unit_point_swap_iso`.
- Normalized 7.15: `normalizedExtend`, `NormalizedFunction`, `NormalizedSupportedFunction`,
  `normalizedSupportedForget`, `normalizedSupportedJacobian`, `normalizedIntegral`,
  `normalizedSupportedIntegral`, `normalized_supported_integral_generator`,
  `gamma_named_normalized_linear_theorem_7_15`, `gamma_named_normalized_theorem_7_15`.
- AE descent: `presentation_ae_of_generic_rows`.
- Head-integral coefficient linearity: `presentation_head_left_product_ae`,
  `ae_head_integral_positive_coefficient`, `head_left_product_common`,
  `presentation_head_zero_coef_ae`, `head_zero_coef_common`, `presentation_head_pos_zero_ae`,
  `head_pos_zero_common`, `presentation_head_zero_zero_ae`, `head_zero_zero_common`.
- Head-linearity tools (namespace `Section7`): `SelectedVFVolumeFamily.Gamma.headFibre`,
  `gamma_head_fibre_standard_contraction`, `head_fibre_integral_volume_iso_gamma`,
  `HK.ZeroVFVolumeFamily.Gamma.headFibre`, `gamma_zero_head_fibre_standard_contraction`,
  `gamma_field_unary_special_preparation`, `VolumeObjectGamma.canonicalVolumeLabels`,
  `rv_coordinate_density_native_iso_gamma`, `HK.ZeroRVVolumeObject.Gamma.zeroRVNativeDensity`,
  `SelectedVFVolumeFamily.Gamma.coordinateSelectedCoefficient`,
  `gamma_unary_special_standard_contraction`, `head_fibre_left_product_row_class`,
  `coordinate_selected_coefficient_row_class`, `CommonContextVolumeEquivalent.of_extend_context`,
  `.reduce`, `.zeroProd`.
- Graded head, permutation, prefix and coordinate integrals; linear 7.11: `pres_head_act`,
  `ae_head_comp_act`, `gradedHeadLinearMap`, `graded_head_of`, `graded_head_fubini`,
  `gradedUnivEquiv`, `gradedPermuteLinearMap`, `graded_permute_of`, `graded_permute_of_zero`,
  `graded_permute_fubini`, `gradedReindexBase`, `graded_reindex_base_fubini`,
  `gradedPrefixLinearMap`, `graded_prefix_of`, `graded_prefix_fubini`,
  `gradedCoordinateIntegralLinearMap`, `graded_coordinate_integral_of`,
  `graded_coordinate_integral_of_zero`, `gamma_named_linear_proposition_7_11`,
  `gamma_named_linear_two_projection_fubini`, `gamma_named_linear_theorem_7_14`.
- Normalized 7.14: `normalizedCoordinateIntegral`, `normalized_coordinate_integral_generator`,
  `gamma_named_normalized_linear_fubini`, `gamma_named_normalized_linear_theorem_7_14`,
  `gamma_named_normalized_theorem_7_14`.
- Internal certificate lemmas `gamma_native_coefficient_preparation_exists`,
  `coordinate_coefficient_contraction_product_iso_gamma`, their zero and finite-coefficient
  versions, `raw_standard_vf_contraction` and `GammaFun.zero_head_row_contraction` take a names
  hypothesis on an arbitrary context (they certify predecessor constructions parameterized by
  one); they are used only with the named code context or frozen generated contexts, where it is
  proved, and are not headlines.
- Gamma tools (namespace `Section7`): `VFVolumeObjectGamma.prod`, `.permuteVF`, `.weightedZero`,
  `VFVolumeIso.GammaDefinable.prod`, `volume_lift_product_iso_gamma`,
  `weighted_lift_zero_product_iso_gamma`, `selected_positive_coefficient_appended_lift_gamma`,
  `SelectedVFVolumeFamily.Gamma.appendedFullLift`, `.weightedZero`,
  `DefinableVFVolumeFamily.Gamma.toSelected`, `HK.ZeroVFVolumeFamily.Gamma.positiveProduct`,
  `.prodZero`, `CommonContextVolumeEquivalent.prod`; contraction lemmas
  `GammaNamed.gamma_prod_contraction`, `GammaNamed.gamma_vf_permutation_covariance`,
  `GammaNamed.gamma_weighted_zero_contraction`, `GammaFun.presentation_appended_full_lift`,
  `GammaFun.presentation_full_lift_contraction`, `GammaFun.gamma_named_integration_equiv_contraction`.
- Context-generic class laws (namespace `Section7.HK.Ctx`): the laws of `GammaNamedRVProductLaws`,
  `GammaNamedRVProductDistributivity` and `GammaNamedRVSemiring` for an arbitrary code context and
  base, applied in row contexts. `HK.Ctx.GammaNamedRVClasses` is a `def` so its instances never
  apply to the named classes.
- Generic helpers over an arbitrary Gamma base (e.g. `GammaNamed.gamma_prod_contraction`) take
  `commonRealNames G ⊆ C.base`, as the existing `GammaNamed` tools do; they are only used with the
  named code context, where it holds by `gamma_named_code_context_names`. No headline type mentions
  it.

## Migration notes for diamond-integral

- **Section 3 files: only a pin bump is needed.** 41 diamond-integral `section 3` files
  mention `hNames`.
  - Three of them (`GammaGroundRealNamesElimination`, `MeasuredRealGroundObjects`,
    `MeasuredRealGroundVFArrows`) use an unrelated local hypothesis of that name ("the Gamma
    names are definable over the real base"). They import nothing from Integration7.
  - The other 38 use no numbered Section 7 result, no `HK.` class category and nothing from
    7.8 or 7.9. They depend only on the hNames-taking internals of Lemma 7.7's proof (the
    P1/P2/P3/P6 roots: `gammaRVGraphRefinement*`, `rvLabelCut`, `gammaNativePresentation`,
    `uniform_balanced_position_preparation_exists`,
    `independent_rectangle_family_preparations_exists`,
    `frozen_generated_context_contains_names`, and similar).
  - The positive-degree reverse kernel is diamond-integral's own theorem. Its headline
    (Theorem 3.22) carries no `hNames`, because it discharges the condition internally with a
    code context containing the common names.
  - These roots (P1–P4) stay unchanged, and every existing public declaration stays
    byte-stable: the branch is purely additive.
- **Raw objects are not Gamma-named objects.** Raw objects over `C.base` are not
  automatically Gamma-named objects, because the code set changes from `C.base` to the code
  context. A bridge (upward code extension, as in `GammaVolumeObjects.extend`) is not provided
  as a public map on classes.
- **Function-level uses.** The additive Gamma-named 7.11/7.12, the homogeneous 7.14/7.15, the
  linear 7.11/7.12 and the normalized 7.14/7.15 are available without `hNames` (the last four on
  `gamma-linear-section7`). The linear 7.11 and normalized 7.14 are unsupported formulations,
  retained by author decision (see the formulation note).

## Verification

- `lake build Integration7.Library` with the local provider passed: 13,523 jobs, exit 0.
- `section 7/verification/hnames-removal/receipt.json` is a PASS for the 132 headline types and
  axioms (45 class-level in `HNamesAudit.log`, 87 function-layer in `FunctionLayerAudit.log`). Only `propext`, `Classical.choice` and `Quot.sound` occur, and `hNames` appears in
  no exported type.
- On `gamma-linear-section7`: `lake build Integration7.Library` passed (13,568 jobs, exit 0), and
  `LinearLayerAudit.log` checks 146 linear-layer headline types and axioms with the same result.
- The provider's 18 new Section 9 headlines are in `scripts/verify_ci.py` SECTION9_HEADLINES
  and were audited on that branch.
