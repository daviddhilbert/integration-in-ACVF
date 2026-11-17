module

public import Integration7.PositiveVolumeClassExtensions
public import Integration7.OrdinaryVolumeCoefficientScalarRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive volume-class extension is semilinear over the actual
ordinary coefficient extension. This records compatibility of parameter
enlargement with the finite-factor scalar operation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem ordinary_volume_coefficient_extend_trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D E : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hDE : (D.base : Set M) ⊆ (E.base : Set M))
    (z : RVVolumeBlowupClasses hc C 0) :
    ordinaryVolumeCoefficientExtend hc D E hDE (ordinaryVolumeCoefficientExtend hc C D hCD z) =
      ordinaryVolumeCoefficientExtend hc C E (fun _ h => hDE (hCD h)) z :=
  Quotient.inductionOn z (fun Z => rfl)

theorem positive_volume_class_extend_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) {k : ℕ}
    (z : RVVolumeBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassExtend hc C D hCD k (z • v) =
      ordinaryVolumeCoefficientExtend hc C D hCD z • positiveVolumeClassExtend hc C D hCD k v := by
  rw [ordinary_volume_coefficient_smul_eq_right_product,ordinary_volume_coefficient_smul_eq_right_product]
  induction z using Quotient.inductionOn with
  | h Z =>
    induction v using Quotient.inductionOn with
    | h U =>
      exact positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_preserving_coordinates_full hc D
        (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
        (fun _ => rfl) (fun _ => rfl))

def positiveVolumeClassExtendSemilinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (k : ℕ) :
    PositiveVolumeBlowupClasses hc C k →ₛₗ[ordinaryVolumeCoefficientExtend hc C D hCD]
      PositiveVolumeBlowupClasses hc D k where
  toAddHom := positiveVolumeClassExtend hc C D hCD k
  map_smul' z v := positive_volume_class_extend_smul hc C D hCD z v

end IntegrationInACVF.Section7
