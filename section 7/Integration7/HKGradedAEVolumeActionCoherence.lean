module

public import Integration7.HKGradedAEVolumeWeightedBilinearity
public import Integration7.GradedSemiringActions
public import Integration7.HKAEZeroPositiveCoefficientAssociativity
public import Integration7.AERVVolumePositiveCoefficientAssociativity

@[expose] public section

/-! The genuine homogeneous coefficient actions satisfy the unit and
all mixed associativity laws, and hence give the full graded semimodule. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem rv_volume_zero_product_smul_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (j : ℕ)
    (z : RVBlowupClasses hc C 0) (u : RVBlowupClasses hc C j) :
    HEq (rvVolumeBlowupClassesProduct hc C 0 j z u) (z • u) :=
  (eqRec_heq _ _).symm

theorem ae_volume_component_action_heq
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ)
    {i i' j j' : ℕ} (hi : i=i') (hj : j=j')
    {u : RVBlowupClasses hc C i} {v : RVBlowupClasses hc C i'}
    {f : AEVolumeFunctionComponent hc C n j} {g : AEVolumeFunctionComponent hc C n j'}
    (hu : HEq u v) (hf : HEq f g) :
    HEq (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C n i' j' v g) := by
  cases hi
  cases hj
  cases hu
  cases hf
  rfl

theorem ae_volume_component_action_assoc
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n i j k : ℕ)
    (u : RVBlowupClasses hc C i) (v : RVBlowupClasses hc C j)
    (f : AEVolumeFunctionComponent hc C n k) :
    HEq (aeVolumeFunctionComponentCoefficientBiadditive hc C n (i+j) k
      (rvVolumeBlowupClassesProduct hc C i j u v) f)
      (aeVolumeFunctionComponentCoefficientBiadditive hc C n i (j+k) u
        (aeVolumeFunctionComponentCoefficientBiadditive hc C n j k v f)) := by
  cases i with
  | zero =>
    exact (ae_volume_component_action_heq hc C n (Nat.zero_add j) rfl
      (rv_volume_zero_product_smul_heq hc C j u v) (HEq.rfl : HEq f f)).trans
        ((heq_of_eq (ae_volume_component_action_smul_left hc C n j k u v f)).trans
          (ae_volume_component_zero_coefficient_heq hc C n (j+k) u
            (aeVolumeFunctionComponentCoefficientBiadditive hc C n j k v f)).symm)
  | succ p =>
    cases j with
    | zero =>
      rw [← zero_volume_coefficient_smul_eq_right_product hc C v u,
        ae_volume_component_action_smul_left]
      exact ((ae_volume_component_action_heq hc C n rfl (Nat.zero_add k)
        (HEq.rfl : HEq u u) (ae_volume_component_zero_coefficient_heq hc C n k v f)).trans
          (heq_of_eq (ae_volume_component_action_smul_right hc C n (p+1) k v u f))).symm
    | succ q =>
      cases k with
      | zero => exact heq_of_eq (ae_zero_positive_coefficient_assoc hc C u v f).symm
      | succ r => exact ae_rv_volume_positive_coefficient_assoc hc C u v f

def aeVolumeFunctionGradedAction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    GradedSemiringAction (RVBlowupClasses hc C) (AEVolumeFunctionComponent hc C n) where
  act := aeVolumeFunctionComponentCoefficientBiadditive hc C n
  one_act := ae_volume_component_one_action hc C n
  mul_act := ae_volume_component_action_assoc hc C n

instance gradedAEVolumeFunctionModule
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n : ℕ) :
    Module (RVVolumeBlowupSemiring hc C) (GradedAEVolumeFunction hc C n) :=
  gradedSemiringActionModule (aeVolumeFunctionGradedAction hc C n)

theorem graded_ae_volume_coefficient_action_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n i j : ℕ)
    (u : RVBlowupClasses hc C i) (f : AEVolumeFunctionComponent hc C n j) :
    DirectSum.of (RVBlowupClasses hc C) i u • DirectSum.of (AEVolumeFunctionComponent hc C n) j f =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (i+j)
        (aeVolumeFunctionComponentCoefficientBiadditive hc C n i j u f) :=
  graded_semiring_action_of_of (aeVolumeFunctionGradedAction hc C n) i j u f

end IntegrationInACVF.Section7.HK
