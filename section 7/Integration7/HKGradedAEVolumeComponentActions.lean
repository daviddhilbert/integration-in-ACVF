import Integration7.HKGradedAEVolumeFunctions
import Integration7.HKAEZeroPositiveCoefficientLinearMaps
import Integration7.HKAERVPositiveCoefficientWeightedBilinearity
import Mathlib.Algebra.Module.End

/-! All four homogeneous coefficient actions, including ordinary degree
zero, on the actual graded AE function components. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {a b : ℕ}

def aeVolumeFunctionComponentDegreeLinearEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) (h : a=b) :
    AEVolumeFunctionComponent hc C n a ≃ₗ[RVBlowupClasses hc C 0] AEVolumeFunctionComponent hc C n b := by
  cases h
  exact LinearEquiv.refl _ _

theorem ae_volume_function_component_degree_symm_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) (h : a=b)
    (f : AEVolumeFunctionComponent hc C n b) :
    HEq ((aeVolumeFunctionComponentDegreeLinearEquiv hc C n h).symm f) f := by
  cases h
  rfl

def aeVolumeFunctionComponentCoefficientBiadditive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n i j : ℕ) :
    RVBlowupClasses hc C i →+ (AEVolumeFunctionComponent hc C n j →+ AEVolumeFunctionComponent hc C n (i+j)) := by
  cases i with
  | zero =>
    let e := aeVolumeFunctionComponentDegreeLinearEquiv hc C n (Nat.zero_add j)
    exact (AddMonoidHom.compHom e.symm.toAddMonoidHom).comp
      (smulAddHom (RVBlowupClasses hc C 0) (AEVolumeFunctionComponent hc C n j))
  | succ p =>
    cases j with
    | zero => exact aeZeroVolumeFunctionPositiveCoefficientBiadditive hc C n p
    | succ k => exact aeRVVolumeFunctionPositiveCoefficientBiadditive hc C n p k

theorem ae_volume_component_zero_coefficient_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ)
    (z : RVBlowupClasses hc C 0) (f : AEVolumeFunctionComponent hc C n j) :
    HEq (aeVolumeFunctionComponentCoefficientBiadditive hc C n 0 j z f) (z • f) :=
  ae_volume_function_component_degree_symm_heq hc C n (Nat.zero_add j) (z • f)

@[simp] theorem ae_volume_component_positive_zero_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AEZeroVolumeFunction hc C n) :
    aeVolumeFunctionComponentCoefficientBiadditive hc C n (p+1) 0 u f =
      aeZeroVolumeFunctionPositiveCoefficientProduct hc C n p u f := rfl

@[simp] theorem ae_volume_component_positive_positive_coefficient
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n p k : ℕ)
    (u : PositiveVolumeBlowupClasses hc C p) (f : AERVVolumeFunction hc C n k) :
    aeVolumeFunctionComponentCoefficientBiadditive hc C n (p+1) (k+1) u f =
      aeRVVolumeFunctionPositiveCoefficientProduct hc C n p k u f := rfl

theorem ae_volume_component_one_action
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n j : ℕ)
    (f : AEVolumeFunctionComponent hc C n j) :
    HEq (aeVolumeFunctionComponentCoefficientBiadditive hc C n 0 j GradedMonoid.GOne.one f) f := by
  change HEq (aeVolumeFunctionComponentCoefficientBiadditive hc C n 0 j (1 : RVBlowupClasses hc C 0) f) f
  exact (ae_volume_component_zero_coefficient_heq hc C n j 1 f).trans (heq_of_eq (one_smul _ f))

end IntegrationInACVF.Section7.HK
