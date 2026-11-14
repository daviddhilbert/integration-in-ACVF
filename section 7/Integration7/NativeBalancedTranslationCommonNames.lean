import Integration7.NativeBalancedTranslations
import Integration7.BalancedInversePositionGraphs
import Integration7.GammaNamesVolumeContexts
import Integration7.NativeRelativeTranslationVolumes

/-! Actual definable balanced-cell translations, with original-base centre
graphs and Jacobian-one certificates. A containing small context realizes
the names; the graph certificates retain the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section4.BalancedFibres
open IntegrationInACVF.Section4.Cells IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {D E : Set (VF (M := M))} {f : VF (M := M) → VF (M := M)} {r t : RV (M := M)}

theorem balanced_translation_centres_over_common_names
    {B : Base (M := M)} (hNames : commonRealNames B ⊆ S)
    (A : DefSet (M := M) S 2 0) (hA : GammaSetDefinable B (carrier A))
    (h : HasBalancedFibres D E (nativeVFPairDomain A) f r t)
    (hf : DefinableOverBase B (fun _ : Fin 2 => .vf) (positionCodes D f)) :
    ∃ K : BalancedTranslationCentres A h,
      GammaScalarGraphDefinable B (fun p z => ∃ q : A,
        q.val = p ∧ (K.vertical q).val 0 = z) ∧
      GammaScalarGraphDefinable B (fun p z => ∃ q : A,
        q.val = p ∧ (K.horizontal q).val 0 = z) := by
  have hg := balanced_inverse_position_graph h hf
  have hf' := hf.common_names.mono hNames
  have hg' := hg.common_names.mono hNames
  let K := balancedTranslationCentresOfPositionGraphs A h hf' hg'
  refine ⟨K,?_,?_⟩
  · exact coordinate_position_native_gamma_graph A hA 0 D f hf' hf
      (fun p => (h.subset ⟨p.val,p.property,rfl⟩).1)
  · exact coordinate_position_native_gamma_graph A hA 1 E (balancedInversePosition h) hg' hg
      (fun p => (h.subset ⟨p.val,p.property,rfl⟩).2)

end IntegrationInACVF.Section7
