module

public import Integration7.UniformCellVerticalTranslations
public import Integration7.UnaryPullbackCommonNamePreparations
public import Integration7.UnarySpecialHeadPreparations
public import IntegrationSection6.StandardProgramPresentations

@[expose] public section

/-! The uniform vertical translation has an actual standard contraction:
its complete vertical RV fibres contract by identity, and the remaining
unary domain is prepared over the same fixed common names. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

namespace UniformMixedCellPresentation

theorem vertical_translation_standard_contraction_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A)) :
    ∃ E : StandardContraction (F.verticalTranslationImage hNames) (Equiv.refl _), GammaProgramDefinable G E.program := by
  let Y := F.verticalTranslationImage hNames
  have hY := F.vertical_translation_image_gamma hNames
  let H : HeadPreparation Y := ⟨m+F.arity,Y,Map.id Y,specialRelative_id Y 0,F.vertical_translation_head_saturated hNames⟩
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    H.contractedSet (gamma_headImage Y hY)
  let P := OrderedContractionProgram.step H (unarySpecialContractionProgram T hD)
  have hP : GammaProgramDefinable G P :=
    ⟨gamma_identity_graph Y hY,hY,gamma_unary_special_contraction_program T hD hT⟩
  let E := standardFromProgram Y (Equiv.refl _) P (vfPermutationImage_id_eq Y).symm
  exact ⟨E,gamma_standardFromProgram Y _ P _ hP⟩

end UniformMixedCellPresentation
end IntegrationInACVF.Section7
