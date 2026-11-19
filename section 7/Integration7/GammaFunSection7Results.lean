import Integration7.GammaFunZeroCoordinate

/-! Gamma-named Propositions 7.11 and 7.12 on homogeneous Gamma-named functions, with values in
the Gamma-named RV semiring. No `hNames` hypothesis: functions are presentations coded over
the named code context and Gamma over `⟨C.base, Ξ⟩`; integrals are Gamma-named classes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem gamma_semiring_of_heq {d d' : ℕ} (h : d = d')
    {x : HK.GammaNamedRVClasses hc C Ξ hΞ (d+1)} {x' : HK.GammaNamedRVClasses hc C Ξ hΞ (d'+1)} (hx : HEq x x') :
    DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (d+1) x = DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (d'+1) x' := by
  subst h
  rw [eq_of_heq hx]

/-- **The Gamma-named integral of a positive almost-everywhere function**, in the Gamma-named
RV semiring. -/
def gammaSemiringIntegral (f : AEFunction hc C Ξ hΞ n k) : HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) k + 1)
    (aeAppendedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f)

/-- **The Gamma-named integral of a weighted degree-zero almost-everywhere function**, in the
Gamma-named RV semiring. -/
def gammaSemiringZeroIntegral (f : AEZeroFunction hc C Ξ hΞ n) : HK.GammaNamedRVSemiring hc C Ξ hΞ :=
  DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1) (aeZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f)

/-- **Gamma-named Proposition 7.11 (positive functions).** Integration along any VF coordinate
projection followed by integration over the retained coordinates equals total integration. -/
theorem gamma_named_proposition_7_11 (E : VFCoordinateProjection (n+1) (p+1)) (f : AEFunction hc C Ξ hΞ n k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E f) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := by
  apply gamma_semiring_of_heq hc C Ξ hΞ _ (ae_coordinate_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 E f)
  simp only [append_volume_degree_eq]
  have h := volume_projection_index_eq E
  omega

/-- **Gamma-named Proposition 7.11 (weighted degree-zero functions).** -/
theorem gamma_named_proposition_7_11_zero (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ}
    (hr : E.discarded = r+1) (f : AEZeroFunction hc C Ξ hΞ n) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f) =
      gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f := by
  apply gamma_semiring_of_heq hc C Ξ hΞ _ (ae_zero_coordinate_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f)
  simp only [append_volume_degree_eq]
  have h := volume_projection_index_eq E
  omega

/-- **Gamma-named Proposition 7.11 (weighted degree-zero functions, no discarded coordinate).** The
retained-coordinate reordering preserves the integral. -/
theorem gamma_named_proposition_7_11_zero_permute (σ : Equiv.Perm (Fin (n+1))) (f : AEZeroFunction hc C Ξ hΞ n) :
    gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroPermute hc C Ξ hΞ σ f) =
      gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 f :=
  congrArg (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1)) (ae_zero_permute_integral hc C Ξ hΞ hGenerated γ hγ hγ1 σ f)

/-- **Gamma-named Proposition 7.12 (positive functions).** The Gamma Jacobian transform along a
Gamma VF bijection preserves the Gamma-named integral of supported functions. -/
theorem gamma_named_proposition_7_12 {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEFunction hc C Ξ hΞ X k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ Y (supportedJacobian hc C Ξ hΞ φ f)) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ X f) :=
  congrArg (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (appendVolumeDegree (n+1) k + 1))
    (supported_jacobian_appended_integral hc C Ξ hΞ hGenerated γ hγ hγ1 φ f)

/-- **Gamma-named Proposition 7.12 (weighted degree-zero functions).** -/
theorem gamma_named_proposition_7_12_zero {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEZeroFunction hc C Ξ hΞ X) :
    gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (supportedZeroForget hc C Ξ hΞ Y (supportedZeroJacobian hc C Ξ hΞ φ f)) =
      gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedZeroForget hc C Ξ hΞ X f) :=
  congrArg (DirectSum.of (HK.GammaNamedRVClasses hc C Ξ hΞ) (n+1))
    (supported_zero_jacobian_integral hc C Ξ hΞ hGenerated γ hγ hγ1 φ f)

end IntegrationInACVF.Section7.GammaFun
