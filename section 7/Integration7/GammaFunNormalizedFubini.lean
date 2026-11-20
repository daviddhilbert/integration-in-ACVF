import Integration7.GammaFunNormalizedResults
import Integration7.GammaFunGradedCoordinate

/-! **Gamma-named normalized Fubini (Theorem 7.14).** The normalized coordinate integral is the
scalar extension of the linear graded coordinate integral along the normalization map
`HK.GammaNamedRVSemiring → HK.NormalizedGammaRVRing`; normalized Fubini and Theorem 7.14 follow from
linear Proposition 7.11 by the universal property. Stated on all normalized Gamma-named functions
on `VF^(n+1)` (no support set). No hypothesis puts the common names of `⟨C.base, Ξ⟩` into
`C.base`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

set_option quotPrecheck false
local notation "𝔑" => HK.NormalizedGammaRVRing hc C Ξ hΞ
local notation "ν" => HK.normalizedGammaCoefficientMap hc C Ξ hΞ

/-- **The normalized Gamma-named coordinate integral** along a VF coordinate projection: the scalar
extension of the linear graded coordinate integral. -/
def normalizedCoordinateIntegral (E : VFCoordinateProjection (n+1) (p+1)) :
    NormalizedFunction hc C Ξ hΞ n →ₗ[𝔑] NormalizedFunction hc C Ξ hΞ p :=
  normalizedExtend hc C Ξ hΞ (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E)

theorem normalized_coordinate_integral_generator (E : VFCoordinateProjection (n+1) (p+1))
    (f : GradedAEFunction hc C Ξ hΞ n) :
    normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E (scalarExtensionGenerator ν _ f) =
      scalarExtensionGenerator ν _ (gradedCoordinateIntegralLinearMap hc C Ξ hΞ hGenerated γ hγ hγ1 E f) :=
  normalized_extend_generator hc C Ξ hΞ _ f

include hγ hγ1 in
/-- **Normalized Gamma-named Fubini (linear form).** For every VF coordinate projection `E`, the
normalized integral over the retained coordinates composed with the normalized coordinate integral
is the normalized integral. -/
theorem gamma_named_normalized_linear_fubini (E : VFCoordinateProjection (n+1) (p+1)) :
    (normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 p).comp
        (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E) =
      normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 n := by
  apply scalar_extension_linearMap_ext ν
  intro f
  change normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 p
    (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 E (scalarExtensionGenerator ν _ f)) = _
  rw [normalized_coordinate_integral_generator,normalized_integral_generator,normalized_integral_generator,
    ← gamma_named_linear_proposition_7_11 hc C Ξ hΞ hGenerated γ hγ hγ1 E]
  rfl

include hγ hγ1 in
/-- **Gamma-named Theorem 7.14 (normalized, linear form).** For nonempty VF coordinate sets `E`
and `F`, the normalized iterated integrals along the two retained-coordinate projections agree. -/
theorem gamma_named_normalized_linear_theorem_7_14 (E F : Set (Fin (n+1))) (hE : E.Nonempty) (hF : F.Nonempty) :
    (normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 _).comp
        (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection E hE)) =
      (normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 _).comp
        (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection F hF)) := by
  rw [gamma_named_normalized_linear_fubini hc C Ξ hΞ hGenerated γ hγ hγ1,
    gamma_named_normalized_linear_fubini hc C Ξ hΞ hGenerated γ hγ hγ1]

include hγ hγ1 in
/-- **Gamma-named Theorem 7.14 (normalized).** Normalized Fubini for two nonempty VF coordinate
sets, on all normalized Gamma-named functions. -/
theorem gamma_named_normalized_theorem_7_14 (E F : Set (Fin (n+1))) (hE : E.Nonempty) (hF : F.Nonempty)
    (f : NormalizedFunction hc C Ξ hΞ n) :
    normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 _
        (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection E hE) f) =
      normalizedIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 _
        (normalizedCoordinateIntegral hc C Ξ hΞ hGenerated γ hγ hγ1 (nonemptyVolumeCoordinateProjection F hF) f) :=
  LinearMap.congr_fun (gamma_named_normalized_linear_theorem_7_14 hc C Ξ hΞ hGenerated γ hγ hγ1 E F hE hF) f

end IntegrationInACVF.Section7.GammaFun
