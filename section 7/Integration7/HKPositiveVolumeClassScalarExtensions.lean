module

public import Integration7.PositiveVolumeClassExtensions
public import Integration7.HKZeroCoefficientScalarRows
public import Integration7.HKZeroCoefficientExtensions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Positive volume-class extension is semilinear over the actual
weighted coefficient extension. This records compatibility of parameter
enlargement with the finite-factor scalar operation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem zero_volume_coefficient_extend_trans
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D E : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hDE : (D.base : Set M) ⊆ (E.base : Set M))
    (z : RVBlowupClasses hc C 0) :
    zeroVolumeCoefficientExtend hc D E hDE (zeroVolumeCoefficientExtend hc C D hCD z) =
      zeroVolumeCoefficientExtend hc C E (fun _ h => hDE (hCD h)) z :=
  Quotient.inductionOn z (fun Z => rfl)

theorem weighted_positive_volume_class_extend_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) {k : ℕ}
    (z : RVBlowupClasses hc C 0) (v : PositiveVolumeBlowupClasses hc C k) :
    positiveVolumeClassExtend hc C D hCD k (z • v) =
      zeroVolumeCoefficientExtend hc C D hCD z • positiveVolumeClassExtend hc C D hCD k v := by
  rw [zero_volume_coefficient_smul_eq_right_product,zero_volume_coefficient_smul_eq_right_product]
  induction z using Quotient.inductionOn with
  | h Z =>
    induction v using Quotient.inductionOn with
    | h U =>
      exact positiveVolumeBlowupClass_iso hc D (RVVolumeIso.of_preserving_coordinates_full hc D
        (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection (Map.id _) Function.bijective_id (fun _ => rfl)))
        (fun _ => rfl) (fun _ => rfl))

def weightedPositiveVolumeClassExtendSemilinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (k : ℕ) :
    PositiveVolumeBlowupClasses hc C k →ₛₗ[zeroVolumeCoefficientExtend hc C D hCD]
      PositiveVolumeBlowupClasses hc D k where
  toAddHom := positiveVolumeClassExtend hc C D hCD k
  map_smul' z v := weighted_positive_volume_class_extend_smul hc C D hCD z v

end IntegrationInACVF.Section7.HK
