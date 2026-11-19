import Integration7.GammaFunAEAdditiveMaps
import Integration7.NonemptyVolumeCoordinateProjections

/-! Gamma-named Propositions 7.11, 7.12 and Theorems 7.14, 7.15 for Gamma-named functions as
additive monoid homomorphisms, with values in the Gamma-named RV semiring. The coordinate
integrals, Jacobian transforms and integrals are additive; integration along a coordinate
projection followed by integration of the retained coordinates is total integration (7.11),
Jacobian transforms preserve the integral (7.12), any two coordinate projections give the same
iterated integral (7.14), and change of variables holds (7.15). No `hNames` hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

/-- **Gamma-named Proposition 7.11 (additive form).** -/
theorem gamma_named_proposition_7_11_add_hom (E : VFCoordinateProjection (n+1) (p+1)) (k : ℕ) :
    (gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 p (appendVolumeDegree E.discarded k)).comp
        (aeCoordinateIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 E k) =
      gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k :=
  AddMonoidHom.ext (gamma_named_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1 E)

/-- **Gamma-named Proposition 7.11 for weighted degree-zero functions (additive form).** -/
theorem gamma_named_proposition_7_11_zero_add_hom (E : VFCoordinateProjection (n+1) (p+1)) {r : ℕ}
    (hr : E.discarded = r+1) :
    (gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 p (appendVolumeDegree r 0)).comp
        (aeZeroCoordinateIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 E hr) =
      gammaSemiringZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n :=
  AddMonoidHom.ext (gamma_named_proposition_7_11_zero hc C Ξ hΞ hGenerated γ hγ hγ1 E hr)

/-- **Gamma-named Proposition 7.12 (additive form).** -/
theorem gamma_named_proposition_7_12_add_hom {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) (k : ℕ) :
    ((gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k).comp (supportedForgetAddHom hc C Ξ hΞ Y k)).comp
        (supportedJacobianAddHom hc C Ξ hΞ φ k) =
      (gammaSemiringIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n k).comp (supportedForgetAddHom hc C Ξ hΞ X k) :=
  AddMonoidHom.ext (gamma_named_proposition_7_12 hc C Ξ hΞ hGenerated γ hγ hγ1 φ)

/-- **Gamma-named Proposition 7.12 for weighted degree-zero functions (additive form).** -/
theorem gamma_named_proposition_7_12_zero_add_hom {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    ((gammaSemiringZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (supportedZeroForgetAddHom hc C Ξ hΞ Y)).comp
        (supportedZeroJacobianAddHom hc C Ξ hΞ φ) =
      (gammaSemiringZeroIntegralAddHom hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (supportedZeroForgetAddHom hc C Ξ hΞ X) :=
  AddMonoidHom.ext (gamma_named_proposition_7_12_zero hc C Ξ hΞ hGenerated γ hγ hγ1 φ)

/-- Two coordinate projections give the same iterated Gamma-named integral. -/
theorem gamma_named_two_projection_fubini (E : VFCoordinateProjection (n+1) (p+1))
    (F : VFCoordinateProjection (n+1) (q+1)) (f : AEFunction hc C Ξ hΞ n k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E f) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 F f) :=
  (gamma_named_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1 E f).trans
    (gamma_named_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1 F f).symm

/-- **Gamma-named Theorem 7.14 (positive functions).** For nonempty coordinate sets `E` and `F`,
integrating out the complement of `E` and then `E` gives the same Gamma-named class as for `F`. -/
theorem gamma_named_theorem_7_14 (E F : Set (Fin (n+1))) (hE : E.Nonempty) (hF : F.Nonempty)
    (f : AEFunction hc C Ξ hΞ n k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection E hE) f) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (aeCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection F hF) f) :=
  gamma_named_two_projection_fubini hc C Ξ hΞ hGenerated γ hγ hγ1 _ _ f

/-- **Gamma-named Theorem 7.14 (weighted degree-zero functions)**, for coordinate projections that
each discard at least one coordinate. -/
theorem gamma_named_theorem_7_14_zero (E : VFCoordinateProjection (n+1) (p+1)) (F : VFCoordinateProjection (n+1) (q+1))
    {r s : ℕ} (hr : E.discarded = r+1) (hs : F.discarded = s+1) (f : AEZeroFunction hc C Ξ hΞ n) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (aeZeroCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 F hs f) :=
  (gamma_named_proposition_7_11_zero hc C Ξ hΞ hGenerated γ hγ hγ1 E hr f).trans
    (gamma_named_proposition_7_11_zero hc C Ξ hΞ hGenerated γ hγ hγ1 F hs f).symm

/-- **Gamma-named Theorem 7.15 (positive functions).** Change of variables along a Gamma VF bijection. -/
theorem gamma_named_theorem_7_15 {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEFunction hc C Ξ hΞ X k) :
    gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ X f) =
      gammaSemiringIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedForget hc C Ξ hΞ Y (supportedJacobian hc C Ξ hΞ φ f)) :=
  (gamma_named_proposition_7_12 hc C Ξ hΞ hGenerated γ hγ hγ1 φ f).symm

/-- **Gamma-named Theorem 7.15 (weighted degree-zero functions).** -/
theorem gamma_named_theorem_7_15_zero {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : SupportedAEZeroFunction hc C Ξ hΞ X) :
    gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (supportedZeroForget hc C Ξ hΞ X f) =
      gammaSemiringZeroIntegral hc C Ξ hΞ hGenerated γ hγ hγ1
        (supportedZeroForget hc C Ξ hΞ Y (supportedZeroJacobian hc C Ξ hΞ φ f)) :=
  (gamma_named_proposition_7_12_zero hc C Ξ hΞ hGenerated γ hγ hγ1 φ f).symm

end IntegrationInACVF.Section7.GammaFun
