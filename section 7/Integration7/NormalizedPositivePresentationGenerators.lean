module

public import Integration7.NormalizedPositiveDegreeFunctions
public import Integration7.NormalizedPositiveFunctionGeneration

@[expose] public section

/-! The positive-presentation equivalence has the literal inverse
formula on every positive homogeneous normalized generator. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem normalized_positive_presentation_inverse
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (n k : ℕ)
    (f : AERVVolumeFunction hc C n k) :
    (normalizedPositiveDegreeVolumeEquiv hc C n).symm (normalizedPositiveVolumeFunction hc C n k f) =
      scalarExtensionGenerator (normalizedVolumeCoefficientMap hc C) _
        (DirectSum.of (fun j => AEVolumeFunctionComponent hc C n (j+1)) k f) := by
  apply (normalizedPositiveDegreeVolumeEquiv hc C n).injective
  rw [LinearEquiv.apply_symm_apply,normalized_positive_degree_equiv_generator,graded_shift_to_sum_of]
  rfl
end IntegrationInACVF.Section7
