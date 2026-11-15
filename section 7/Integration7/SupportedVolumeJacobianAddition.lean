import Integration7.SupportedVolumeFunctionAddition
import Integration7.SelectedJacobianRowAddition

/-! The actual Jacobian transform is additive on supported positive
homogeneous AE functions, including its empty-family value. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b k : ℕ}

theorem selected_jacobian_sum_row_class
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) n) (C.base : Set M)}
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (hF : ∀ p : F.domain, p.val.1 ∈ X.carrier) (hG : ∀ p : G.domain, p.val.1 ∈ X.carrier)
    (y : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      (((selectedVolumeFamilySum F G).jacobianPushforward φ hφ
        (selected_volume_family_sum_supported F G hF hG)).rowInContext y) =
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      ((F.jacobianPushforward φ hφ hF).rowInContext y) +
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C y)
      ((G.jacobianPushforward φ hφ hG).rowInContext y) := by
  by_cases hy : y ∈ Y.carrier
  · exact selected_jacobian_row_add_comparison hc C F G (selectedVolumeFamilySum F G)
      φ hφ hF hG (selected_volume_family_sum_supported F G hF hG) ⟨y,hy⟩
      (selected_volume_family_sum_row_class hc F G _)
  · let D := vfParameterVolumeContext C y
    have hEmpty (d : ℕ) (H : SelectedVFVolumeFamily C n d k)
        (hH : ∀ p : H.domain, p.val.1 ∈ X.carrier) :
        positiveVolumeBlowupClass hc D ((H.jacobianPushforward φ hφ hH).rowInContext y) = 0 :=
      positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_empty hc D _ _
        (selected_jacobian_row_empty_outside C H φ hφ hH y hy) rfl)
    rw [hEmpty _ (selectedVolumeFamilySum F G) _,hEmpty _ F _,hEmpty _ G _,zero_add]

theorem supported_volume_jacobian_map_add
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ)
    (f g : SupportedAERVVolumeFunction hc C X k) :
    supportedVolumeFunctionJacobian hc C φ hφ (f+g) =
      supportedVolumeFunctionJacobian hc C φ hφ f +
        supportedVolumeFunctionJacobian hc C φ hφ g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G =>
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (selected_jacobian_sum_row_class hc C F.2.val G.2.val φ hφ
        F.2.property G.2.property y).trans
        (selected_volume_family_sum_row_class hc
          (F.2.val.jacobianPushforward φ hφ F.2.property)
          (G.2.val.jacobianPushforward φ hφ G.2.property) y).symm

theorem supported_volume_jacobian_map_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    supportedVolumeFunctionJacobian hc C φ hφ (0 : SupportedAERVVolumeFunction hc C X k) = 0 := by
  apply Quotient.sound
  apply ae_rv_volume_function_equivalent_of_pointwise hc C
  intro y
  apply positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C y)
  apply RVVolumeIso.of_empty hc (vfParameterVolumeContext C y) _ _ _ rfl
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro r ⟨p,hp⟩
  exact p.property

def supportedVolumeJacobianAddHom
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {X Y : DefSet (rawVFSpace (M := M) (n+1)) (C.base : Set M)}
    (φ : Map X Y) (hφ : Function.Bijective φ) :
    SupportedAERVVolumeFunction hc C X k →+ SupportedAERVVolumeFunction hc C Y k where
  toFun := supportedVolumeFunctionJacobian hc C φ hφ
  map_zero' := supported_volume_jacobian_map_zero hc C φ hφ
  map_add' := supported_volume_jacobian_map_add hc C φ hφ
end IntegrationInACVF.Section7
