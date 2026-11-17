module

public import Integration7.SupportedPositiveVolumeCoefficients
public import Integration7.SelectedJacobianRowProducts
public import Integration7.SupportedVolumeJacobianAddition

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The supported positive Jacobian transform commutes with actual
multiplication by every positive common-blowup coefficient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a k p : ℕ}

theorem selected_jacobian_positive_coefficient_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
    (F : SelectedVFVolumeFamily C n a k) (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ q : F.domain, q.val.1 ∈ X.carrier) (y : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      (((selectedVolumeFamilyLeftProduct U F).jacobianPushforward φ hφ
        (selected_volume_family_left_product_supported U F hF)).rowInContext y) =
    rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C y) (p+1) (k+1)
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C y) (positiveVolumeCoefficientInContext U y))
      (positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
        ((F.jacobianPushforward φ hφ hF).rowInContext y)) := by
  by_cases hy : y ∈ Y.carrier
  · exact selected_jacobian_row_positive_product_comparison hc C U F
      (selectedVolumeFamilyLeftProduct U F) φ hφ hF
      (selected_volume_family_left_product_supported U F hF) ⟨y,hy⟩
      (selected_volume_family_left_product_row_class hc U F _)
  · let D := vfParameterVolumeContext C y
    have hEmpty {d j : ℕ} (H : SelectedVFVolumeFamily C n d j)
        (hH : ∀ q : H.domain, q.val.1 ∈ X.carrier) :
        positiveVolumeBlowupClass hc D ((H.jacobianPushforward φ hφ hH).rowInContext y) = 0 :=
      positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_empty hc D _ _
        (selected_jacobian_row_empty_outside C H φ hφ hH y hy) rfl)
    rw [hEmpty (selectedVolumeFamilyLeftProduct U F) _,hEmpty F _]
    exact (DirectSum.GNonUnitalNonAssocSemiring.mul_zero
      (A := RVVolumeBlowupClasses hc D) (i := p+1) (j := k+1)
      (positiveVolumeBlowupClass hc D (positiveVolumeCoefficientInContext U y))).symm

theorem supported_volume_jacobian_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionJacobian hc C φ hφ (supportedPositiveVolumeCoefficientProduct hc C X u f) =
      supportedPositiveVolumeCoefficientProduct hc C Y u (supportedVolumeFunctionJacobian hc C φ hφ f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (selected_jacobian_positive_coefficient_row_class hc C U F.2.val φ hφ F.2.property y).trans
        (selected_volume_family_left_product_row_class hc U
          (F.2.val.jacobianPushforward φ hφ F.2.property) y).symm
end IntegrationInACVF.Section7
