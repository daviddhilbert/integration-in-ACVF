import Integration7.GammaFunNormalizedResults
import Integration7.GammaFunGenericRows
import Integration7.GammaFunNormalizedFubini

/-! **Entry point of the Gamma-named linear Section 7 results** (extends `Integration7.GammaFunLinearResults`).

Over the Gamma-named base `⟨C.base, Ξ⟩` and its named code context, with no hypothesis putting
common names into `C.base`:

* `GammaFun.gradedAEFunctionModule`: the graded Gamma-named almost-everywhere functions (weighted
  degree zero in component zero, positive coefficient degree `k` in component `k+1`) form a module
  over `HK.GammaNamedRVSemiring`, through the graded semiring action `GammaFun.aeGradedAction`.
* `GammaFun.gradedIntegralLinearMap`: the graded Gamma-named integral is
  `HK.GammaNamedRVSemiring`-linear; on homogeneous elements `GammaFun.comp_integral_act`.
* `GammaFun.supportedGradedFunctionModule`: graded functions supported in a Gamma VF set form a
  module over `HK.GammaNamedRVSemiring`; `GammaFun.suppJacLinearMap` is the linear Jacobian transform.
* `GammaFun.gamma_named_linear_proposition_7_12`: **linear Proposition 7.12** as an equality of
  `HK.GammaNamedRVSemiring`-linear maps.
* `HK.NormalizedGammaRVRing`, `HK.normalizedGammaCoefficientMap`: the Gamma-named point class is
  central (`HK.gamma_point_class_commutes`); localizing at it and normalizing gives the normalized
  coefficient ring, with the point sent to `1`.
* `GammaFun.gamma_named_normalized_linear_theorem_7_15`, `GammaFun.gamma_named_normalized_theorem_7_15`:
  **normalized Theorem 7.15** on the scalar extension of the supported module.
* `GammaFun.presentation_ae_of_generic_rows`: rows at generic points determine AE classes.
* Head integrals commute with every coefficient action: `GammaFun.presentation_head_left_product_ae`
  (positive coefficient, positive function), `GammaFun.presentation_head_zero_coef_ae` (weighted
  degree-zero coefficient, positive function), `GammaFun.presentation_head_pos_zero_ae` (positive
  coefficient, degree-zero function) and `GammaFun.presentation_head_zero_zero_ae` (both degree zero).
* `GammaFun.gradedHeadLinearMap`, `GammaFun.graded_head_fubini`: the graded head integral is linear
  and preserves the graded integral.
* `GammaFun.gradedCoordinateIntegralLinearMap`: the graded coordinate integral along a VF
  coordinate projection, linear; it agrees with `aeCoordinateIntegral`/`aeZeroCoordinateIntegral`
  on components (`GammaFun.graded_coordinate_integral_of`, `GammaFun.graded_coordinate_integral_of_zero`).
* `GammaFun.gamma_named_linear_proposition_7_11`, `GammaFun.gamma_named_linear_theorem_7_14`:
  **linear Proposition 7.11** and the linear form of Theorem 7.14.
* `GammaFun.normalizedCoordinateIntegral`, `GammaFun.gamma_named_normalized_linear_theorem_7_14`,
  `GammaFun.gamma_named_normalized_theorem_7_14`: **normalized Theorem 7.14**.

Linear 7.11 and normalized 7.14 are stated on all (graded, resp. normalized) Gamma-named functions
on `VF^(n+1)`, without a support set; linear 7.12 and normalized 7.15 are stated on supported
functions. -/
