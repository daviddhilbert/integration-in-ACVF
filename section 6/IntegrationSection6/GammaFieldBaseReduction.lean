import IntegrationSection6.GammaVFFieldClosureBases
import IntegrationSection6.GammaDefinableBaseReduction

/-! Naming the generated VF parameter field is a definable extension,
so every actual finite Gamma object and witness can descend afterwards. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def vfFieldBaseReduction (B : Base (M := M)) : GammaDefinableBaseReduction (vfFieldNamedBase B) B where
  real_subset := Set.subset_union_left
  real_definable := by
    intro c hc σ hσ
    rcases hc with hc | hc
    · exact real_definableAtBase B σ _ (definableClosureAt_of_mem hc hσ)
    · exact vfFieldNames_definable B c hc σ hσ
  gamma_definable := gamma_name_definable B

end IntegrationInACVF.Section6
