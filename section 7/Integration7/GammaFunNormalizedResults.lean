import Integration7.GammaFunSupportedLinear
import Integration7.GammaFunNormalizedRing
import Integration7.SemimoduleScalarExtension

/-! **Gamma-named normalized change of variables (Theorem 7.15).** Normalized Gamma-named
functions are the scalar extension of the graded Gamma-named function module along the
normalization map `HK.GammaNamedRVSemiring → HK.NormalizedGammaRVRing`; normalized supported
functions are the scalar extension of the supported graded module. The normalized integral and
Jacobian transform are the induced linear maps, and Theorem 7.15 follows from the linear form of
Proposition 7.12 by the universal property. No hypothesis puts the common names of
`⟨C.base, Ξ⟩` into `C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔑" => HK.NormalizedGammaRVRing hc C Ξ hΞ
local notation "ν" => HK.normalizedGammaCoefficientMap hc C Ξ hΞ

/-- Scalar extension of a `HK.GammaNamedRVSemiring`-linear map to normalized coefficients. -/
def normalizedExtend {A B : Type} [AddCommMonoid A] [Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) A]
    [AddCommMonoid B] [Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) B]
    (L : A →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] B) :
    SemimoduleScalarExtension ν A →ₗ[𝔑] SemimoduleScalarExtension ν B :=
  scalarExtensionLift ν ((scalarExtensionGeneratorHom ν B).comp L.toAddMonoidHom) (fun r x => by
    change scalarExtensionGenerator ν B (L (r • x)) = ν r • scalarExtensionGenerator ν B (L x)
    rw [map_smul]
    exact scalar_extension_generator_smul ν B r (L x))

theorem normalized_extend_generator {A B : Type} [AddCommMonoid A] [Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) A]
    [AddCommMonoid B] [Module (HK.GammaNamedRVSemiring hc C Ξ hΞ) B]
    (L : A →ₗ[HK.GammaNamedRVSemiring hc C Ξ hΞ] B) (x : A) :
    normalizedExtend hc C Ξ hΞ L (scalarExtensionGenerator ν A x) = scalarExtensionGenerator ν B (L x) :=
  scalar_extension_lift_generator _ _ _ x

/-- Normalized Gamma-named functions on `VF^n`. -/
abbrev NormalizedFunction (n : ℕ) := SemimoduleScalarExtension ν (GradedAEFunction hc C Ξ hΞ n)

/-- Normalized Gamma-named functions supported in `X`. -/
abbrev NormalizedSupportedFunction (X : GammaVFSet C Ξ hΞ n) :=
  SemimoduleScalarExtension ν (SupportedGradedFunction hc C Ξ hΞ X)

/-- Forgetting the support of normalized functions. -/
def normalizedSupportedForget (X : GammaVFSet C Ξ hΞ n) :
    NormalizedSupportedFunction hc C Ξ hΞ X →ₗ[𝔑] NormalizedFunction hc C Ξ hΞ n :=
  normalizedExtend hc C Ξ hΞ (suppForgetLinearMap hc C Ξ hΞ X)

/-- **The normalized Gamma-named Jacobian transform.** -/
def normalizedSupportedJacobian {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    NormalizedSupportedFunction hc C Ξ hΞ X →ₗ[𝔑] NormalizedSupportedFunction hc C Ξ hΞ Y :=
  normalizedExtend hc C Ξ hΞ (suppJacLinearMap hc C Ξ hΞ φ)

variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hγ hγ1 in
theorem normalized_integral_generators_smul (n : ℕ) (r : HK.GammaNamedRVSemiring hc C Ξ hΞ)
    (f : GradedAEFunction hc C Ξ hΞ n) :
    ν (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n (r • f)) =
      ν r • ν (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n f) := by
  rw [map_smul,smul_eq_mul,map_mul,smul_eq_mul]

/-- **The normalized Gamma-named integral.** -/
def normalizedIntegral (n : ℕ) : NormalizedFunction hc C Ξ hΞ n →ₗ[𝔑] 𝔑 :=
  scalarExtensionLift ν
    ((ν : HK.GammaNamedRVSemiring hc C Ξ hΞ →+* 𝔑).toAddMonoidHom.comp
      (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n).toAddMonoidHom)
    (normalized_integral_generators_smul hc C Ξ hΞ hGenerated γ hγ hγ1 n)

theorem normalized_integral_generator (n : ℕ) (f : GradedAEFunction hc C Ξ hΞ n) :
    normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n (scalarExtensionGenerator ν _ f) =
      ν (gradedIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 n f) :=
  scalar_extension_lift_generator _ _ _ f

/-- The normalized integral of supported normalized functions. -/
def normalizedSupportedIntegral (X : GammaVFSet C Ξ hΞ n) : NormalizedSupportedFunction hc C Ξ hΞ X →ₗ[𝔑] 𝔑 :=
  (normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n).comp (normalizedSupportedForget hc C Ξ hΞ X)

theorem normalized_supported_integral_generator (X : GammaVFSet C Ξ hΞ n) (f : SupportedGradedFunction hc C Ξ hΞ X) :
    normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 X (scalarExtensionGenerator ν _ f) =
      ν (suppIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 X f) := by
  change normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n
    (normalizedSupportedForget hc C Ξ hΞ X (scalarExtensionGenerator ν _ f)) = _
  rw [normalizedSupportedForget,normalized_extend_generator,normalized_integral_generator]
  rfl

include hγ hγ1 in
/-- **Gamma-named Theorem 7.15 (normalized, linear form).** The normalized supported integral over `Y` composed
with the normalized Jacobian transform of a Gamma VF bijection `φ : X → Y` is the normalized
supported integral over `X`. -/
theorem gamma_named_normalized_linear_theorem_7_15 {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y) :
    (normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 Y).comp (normalizedSupportedJacobian hc C Ξ hΞ φ) =
      normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 X := by
  apply scalar_extension_linearMap_ext ν
  intro f
  change normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 Y
    (normalizedSupportedJacobian hc C Ξ hΞ φ (scalarExtensionGenerator ν _ f)) = _
  rw [normalizedSupportedJacobian,normalized_extend_generator,normalized_supported_integral_generator,
    normalized_supported_integral_generator,← gamma_named_linear_proposition_7_12 hc C Ξ hΞ hGenerated γ hγ hγ1 φ]
  rfl

include hγ hγ1 in
/-- **Gamma-named Theorem 7.15 (normalized).** Normalized change of variables on supported normalized
Gamma-named functions. -/
theorem gamma_named_normalized_theorem_7_15 {X Y : GammaVFSet C Ξ hΞ n} (φ : GammaVFBijection C Ξ hΞ X Y)
    (f : NormalizedSupportedFunction hc C Ξ hΞ X) :
    normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 X f =
      normalizedSupportedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 Y (normalizedSupportedJacobian hc C Ξ hΞ φ f) :=
  (LinearMap.congr_fun (gamma_named_normalized_linear_theorem_7_15 hc C Ξ hΞ hGenerated γ hγ hγ1 φ) f).symm

end IntegrationInACVF.Section7.GammaFun
