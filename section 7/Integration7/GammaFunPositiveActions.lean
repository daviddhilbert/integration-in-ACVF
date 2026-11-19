import Integration7.GammaFunPositiveCoefficients

/-! The action of positive Gamma-named coefficient classes on Gamma-named positive functions:
multiplication by the actual left product. It respects Gamma blowup equivalence of the
coefficient and almost-everywhere equivalence of the function, and is additive in the
function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- The positive coefficient `U` times the presentation `F`. -/
def Presentation.leftProduct (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    Presentation C Ξ hΞ n ((p+1)+k) :=
  ⟨_,selectedVolumeFamilyLeftProduct U.val F.family,F.gamma.leftProduct hc U.property⟩

/-- The coefficient carried to the row context of `x`. -/
def rowCoefficient (U : GammaVolumeObjects 𝔅 𝔖 p) (x : Fin (n+1) → VFType (M := M)) :
    GammaVolumeObjects (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) p :=
  GammaVolumeObjects.changeBase (B := rowGammaBase 𝔅 x)
    (GammaVolumeObjects.extend U (fun _ h => vfParameterVolumeContext_contains 𝔇 x (Or.inl h)))
    (GammaBaseDominated.of_subset Set.subset_union_left (Set.Subset.refl _))

theorem presentation_left_product_row_class (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k)
    (x : Fin (n+1) → VFType (M := M)) :
    (F.leftProduct hc C Ξ hΞ U).rowClass hc C Ξ hΞ x =
      gammaVolumeBlowupClass hc (vfParameterVolumeContext 𝔇 x) (rowGammaBase 𝔅 x)
        ((rowCoefficient C Ξ hΞ U x).prod hc ⟨F.family.rowInContext x,F.gamma.row hc x⟩) :=
  gamma_left_product_row_class hc U.property F.gamma x

theorem row_coefficient_equivalent {U U' : GammaVolumeObjects 𝔅 𝔖 p}
    (h : GammaVolumeBlowupEquivalent 𝔅 𝔖 p U U') (x : Fin (n+1) → VFType (M := M)) :
    GammaVolumeBlowupEquivalent (rowGammaBase 𝔅 x) ((vfParameterVolumeContext 𝔇 x).base : Set M) p
      (rowCoefficient C Ξ hΞ U x) (rowCoefficient C Ξ hΞ U' x) :=
  (h.extend _).changeBase _

/-- **The positive coefficient action respects equivalences.** -/
theorem presentation_left_product_ae {U U' : GammaVolumeObjects 𝔅 𝔖 p} (hU : GammaVolumeBlowupEquivalent 𝔅 𝔖 p U U')
    {F H : Presentation C Ξ hΞ n k} (hF : AEEquivalent hc C Ξ hΞ F H) :
    AEEquivalent hc C Ξ hΞ (F.leftProduct hc C Ξ hΞ U) (H.leftProduct hc C Ξ hΞ U') := by
  obtain ⟨E,hE,hRows⟩ := hF
  refine ⟨E,hE,fun x hx => ?_⟩
  rw [presentation_left_product_row_class,presentation_left_product_row_class]
  apply (gammaVolumeBlowupClass_eq_iff hc _ _).mpr
  exact ((row_coefficient_equivalent C Ξ hΞ hU x).product_right hc _ _).trans hc _ _
    (((gammaVolumeBlowupClass_eq_iff hc _ _).mp (hRows x hx)).product_left hc _ _)

/-- **The action of positive Gamma-named coefficients on Gamma-named positive functions.** -/
def aePositiveCoefficientAction (p : ℕ) :
    GammaVolumeBlowupClasses hc 𝔇 𝔅 p → AEFunction hc C Ξ hΞ n k → AEFunction hc C Ξ hΞ n ((p+1)+k) :=
  Quotient.map₂ (fun U F => F.leftProduct hc C Ξ hΞ U)
    (fun _ _ hU _ _ hF => presentation_left_product_ae hc C Ξ hΞ hU hF)

theorem ae_positive_coefficient_action_mk (U : GammaVolumeObjects 𝔅 𝔖 p) (F : Presentation C Ξ hΞ n k) :
    aePositiveCoefficientAction hc C Ξ hΞ p (gammaVolumeBlowupClass hc 𝔇 𝔅 U) (Quotient.mk _ F) =
      Quotient.mk _ (F.leftProduct hc C Ξ hΞ U) := rfl

end IntegrationInACVF.Section7.GammaFun
