import Integration7.AERVVolumePositiveCoefficientBilinearity
import Integration7.PositiveVolumeClassProductExtensions
import Integration7.AERVVolumeDegreeReindexing

/-! Positive coefficient multiplication acts associatively on actual
AE functions. Only arithmetic homogeneous-degree identifications enter
the statement; the coefficient blocks retain their original order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q k : ℕ}

theorem rv_volume_blowup_classes_product_assoc_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {i j l : ℕ}
    (u : RVVolumeBlowupClasses hc C i) (v : RVVolumeBlowupClasses hc C j) (w : RVVolumeBlowupClasses hc C l) :
    HEq (rvVolumeBlowupClassesProduct hc C (i+j) l (rvVolumeBlowupClassesProduct hc C i j u v) w)
      (rvVolumeBlowupClassesProduct hc C i (j+l) u (rvVolumeBlowupClassesProduct hc C j l v w)) := by
  have h := GradedMonoid.GMonoid.mul_assoc (A := RVVolumeBlowupClasses hc C) ⟨i,u⟩ ⟨j,v⟩ ⟨l,w⟩
  exact (Sigma.ext_iff.mp h).2

theorem ae_rv_volume_positive_coefficient_assoc
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (u : PositiveVolumeBlowupClasses hc C p) (v : PositiveVolumeBlowupClasses hc C q)
    (f : AERVVolumeFunction hc C n k) :
    HEq (aeRVVolumeFunctionPositiveCoefficientProduct hc C n ((p+1)+q) k
      (rvVolumeBlowupClassesProduct hc C (p+1) (q+1) u v) f)
      (aeRVVolumeFunctionPositiveCoefficientProduct hc C n p ((q+1)+k) u
        (aeRVVolumeFunctionPositiveCoefficientProduct hc C n q k v f)) := by
  induction u using Quotient.inductionOn with
  | h U =>
    induction v using Quotient.inductionOn with
    | h V =>
      induction f using Quotient.inductionOn with
      | h F =>
        apply ae_rv_volume_function_class_heq_of_rows hc C (Nat.add_assoc (p+1) (q+1) k)
        intro x
        simp only [selected_volume_family_left_product_row_class]
        change HEq (rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) ((p+1)+(q+1)) (k+1)
          (positiveVolumeClassExtend hc C (vfParameterVolumeContext C x) _ ((p+1)+q)
            (rvVolumeBlowupClassesProduct hc C (p+1) (q+1)
              (positiveVolumeBlowupClass hc C U) (positiveVolumeBlowupClass hc C V))) _)
          (rvVolumeBlowupClassesProduct hc (vfParameterVolumeContext C x) (p+1) ((q+1)+(k+1)) _ _)
        rw [positive_volume_class_extend_product]
        exact rv_volume_blowup_classes_product_assoc_heq hc (vfParameterVolumeContext C x) _ _ _

end IntegrationInACVF.Section7
