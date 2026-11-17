module

public import Integration7.NormalizedPositiveJacobianIntegrals

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Normalization makes the point equal to one, so the ordinary
degree-zero functions are represented by genuine positive functions.
Consequently all normalized linear maps are determined on positive
homogeneous function generators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

theorem normalized_ordinary_function_positive_generator (n : ℕ)
    (f : AEOrdinaryRVVolumeFunction hc C n) :
    normalizedVolumeFunctionGenerator hc C n
      (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 f) =
    normalizedPositiveVolumeFunction hc C n 0
      (aeOrdinaryRVVolumeFunctionPositiveCoefficientProduct hc C n 0
        (positiveVolumeBlowupClass hc C (degreeOnePointVolumeObject (C.base : Set M))) f) := by
  have h := normalized_volume_function_point hc C n
    (DirectSum.of (AEVolumeFunctionComponent hc C n) 0 f)
  rw [volumePointClass,graded_ae_volume_coefficient_action_of] at h
  exact h.symm

theorem normalized_volume_function_linearMap_ext_positive
    {N : Type} [AddCommGroup N] [Module (NormalizedRVVolumeRing hc C) N]
    (n : ℕ) {I J : NormalizedVolumeFunction hc C n →ₗ[NormalizedRVVolumeRing hc C] N}
    (h : ∀ k (f : AERVVolumeFunction hc C n k),
      I (normalizedPositiveVolumeFunction hc C n k f) =
        J (normalizedPositiveVolumeFunction hc C n k f)) : I = J := by
  apply scalar_extension_linearMap_ext (normalizedVolumeCoefficientMap hc C)
  intro f
  change I (normalizedVolumeFunctionGenerator hc C n f) = J (normalizedVolumeFunctionGenerator hc C n f)
  induction f using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero,map_zero]
  | add f g hf hg => rw [map_add,map_add,map_add,hf,hg]
  | of j f =>
    cases j with
    | zero => rw [normalized_ordinary_function_positive_generator]; exact h _ _
    | succ k => exact h k f

end IntegrationInACVF.Section7
