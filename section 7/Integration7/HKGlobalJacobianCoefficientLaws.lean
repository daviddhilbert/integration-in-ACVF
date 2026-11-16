import Integration7.HKGlobalJacobianRepresentatives
import Integration7.HKSelectedJacobianWeightedScalarRows
import Integration7.HKZeroJacobianWeightedScalarRows
import Integration7.HKZeroJacobianPositiveCoefficientRows
import Integration7.HKAEZeroPositiveCoefficientProducts
import Integration7.HKAERVWeightedZeroModules
import Integration7.SupportedVolumeJacobianPositiveCoefficients

/-! Every homogeneous coefficient commutes with the actual global
Jacobian operator, including both measured-zero input and scalar degrees. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k p : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
  (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))) (hφ : Function.Bijective φ)

theorem global_jacobian_positive_weighted_smul
    (z : RVBlowupClasses hc C 0) (f : AERVVolumeFunction hc C n k) :
    aeVolumeComponentJacobianAddHom hc C φ hφ (k+1) (z • f) =
      z • aeVolumeComponentJacobianAddHom hc C φ hφ (k+1) f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      change aeVolumeComponentJacobianAddHom hc C φ hφ (k+1)
        (Quotient.mk _ ⟨_,selectedFamilyWeightedZeroProduct F.2 Z⟩) = _
      rw [global_jacobian_positive_representative,global_jacobian_positive_representative]
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (selected_jacobian_row_weighted_scalar_comparison hc C Z F.2
        (selectedFamilyWeightedZeroProduct F.2 Z) φ hφ (fun _ => Set.mem_univ _)
        (fun _ => Set.mem_univ _) ⟨y,Set.mem_univ _⟩
        (selected_family_weighted_zero_row_scalar hc F.2 Z _)).trans
        (selected_family_weighted_zero_row_scalar hc
          (F.2.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)) Z y).symm

theorem global_jacobian_zero_weighted_smul
    (z : RVBlowupClasses hc C 0) (f : AEZeroVolumeFunction hc C n) :
    aeVolumeComponentJacobianAddHom hc C φ hφ 0 (z • f) =
      z • aeVolumeComponentJacobianAddHom hc C φ hφ 0 f := by
  induction z using Quotient.inductionOn with
  | h Z =>
    induction f using Quotient.inductionOn with
    | h F =>
      change aeVolumeComponentJacobianAddHom hc C φ hφ 0 (Quotient.mk _ ⟨_,F.2.prodZero Z⟩) = _
      rw [global_jacobian_zero_representative,global_jacobian_zero_representative]
      apply Quotient.sound
      apply ae_zero_volume_equivalent_of_pointwise hc C
      intro y
      exact (zero_jacobian_row_weighted_scalar_comparison hc C Z F.2 (F.2.prodZero Z)
        φ hφ (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _) ⟨y,Set.mem_univ _⟩
        (zero_volume_family_scalar_row_class hc F.2 Z _)).trans
        (zero_volume_family_scalar_row_class hc
          (F.2.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)) Z y).symm

theorem global_jacobian_zero_positive_coefficient
    (u : PositiveVolumeBlowupClasses hc C p) (f : AEZeroVolumeFunction hc C n) :
    aeVolumeComponentJacobianAddHom hc C φ hφ (p+1)
        (aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u f) =
      aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u
        (aeVolumeComponentJacobianAddHom hc C φ hφ 0 f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      change aeVolumeComponentJacobianAddHom hc C φ hφ (p+1)
        (Quotient.mk _ ⟨_,selectedZeroFamilyPositiveProduct U F.2⟩) = _
      rw [global_jacobian_positive_representative,global_jacobian_zero_representative]
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (zero_jacobian_row_positive_coefficient_comparison hc C U F.2
        (selectedZeroFamilyPositiveProduct U F.2) φ hφ (fun _ => Set.mem_univ _)
        (fun _ => Set.mem_univ _) ⟨y,Set.mem_univ _⟩
        (selected_zero_family_positive_product_row_class hc U F.2 _)).trans
        (selected_zero_family_positive_product_row_class hc U
          (F.2.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)) y).symm

theorem global_jacobian_positive_positive_coefficient
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    aeVolumeComponentJacobianAddHom hc C φ hφ ((p+1)+(k+1))
        (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f) =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u
        (aeVolumeComponentJacobianAddHom hc C φ hφ (k+1) f) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction f using Quotient.inductionOn with
    | h F =>
      change aeVolumeComponentJacobianAddHom hc C φ hφ (((p+1)+k)+1)
        (Quotient.mk _ ⟨_,selectedVolumeFamilyLeftProduct U F.2⟩) = _
      rw [global_jacobian_positive_representative,global_jacobian_positive_representative]
      apply Quotient.sound
      apply ae_rv_volume_function_equivalent_of_pointwise hc C
      intro y
      exact (selected_jacobian_positive_coefficient_row_class hc C U F.2 φ hφ
        (fun _ => Set.mem_univ _) y).trans
        (selected_volume_family_left_product_row_class hc U
          (F.2.jacobianPushforward φ hφ (fun _ => Set.mem_univ _)) y).symm

end IntegrationInACVF.Section7.HK
