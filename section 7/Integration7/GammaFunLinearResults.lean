import Integration7.GammaFunGradedIntegral

/-! **Entry point of the Gamma-named linear function layer.**

Over the Gamma-named base `⟨C.base, Ξ⟩` and its named code context, with no hypothesis putting
common names into `C.base`:

* `GammaFun.gradedAEFunctionModule`: the graded Gamma-named almost-everywhere functions (weighted
  degree zero in component zero, positive coefficient degree `k` in component `k+1`) form a module
  over `HK.GammaNamedRVSemiring`, through the graded semiring action `GammaFun.aeGradedAction`.
* `GammaFun.gradedIntegralLinearMap`: the graded Gamma-named integral is
  `HK.GammaNamedRVSemiring`-linear; on homogeneous elements `GammaFun.comp_integral_act`.

The linear Jacobian (7.12), head and coordinate integrals (7.11) and the normalized layer
(7.14/7.15) are built on top of this entry point. -/
