module

public import Integration7.UniformBalancedHorizontalTranslations
public import Integration7.UniformBalancedHorizontalFibres
public import Integration7.TranslatedRVCoordinateSaturation
public import Integration7.UnaryPullbackCommonNamePreparations
public import Integration7.UnarySpecialHeadPreparations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The balanced family's actual horizontal translation is saturated
after swapping VF coordinates and admits an original-Gamma standard
contraction in the opposite order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}

theorem horizontal_translation_swapped_head_saturated
    {A : DefSet (M := M) S 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ S) :
    HeadSaturated (carrier (vfPermutationImage (F.horizontalTranslationImage hBalanced hNames) (Equiv.swap 0 1))) :=
  swapped_horizontal_saturated _
    (translated_rv_coordinate_saturated _ 1 (F.horizontalCentreMap hBalanced hNames)
      (F.horizontal_centre_constant hBalanced hNames) (F.source_horizontal_fibre hBalanced hNames))

theorem horizontal_translation_standard_contraction_exists (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) :
    ∃ E : StandardContraction (F.horizontalTranslationImage hBalanced hNames) (Equiv.swap 0 1),
      GammaProgramDefinable G E.program := by
  let Y := F.horizontalTranslationImage hBalanced hNames
  let X := vfPermutationImage Y (Equiv.swap 0 1)
  have hX := gamma_vfPermutationImage Y (F.horizontal_translation_image_gamma hBalanced hNames) (Equiv.swap 0 1)
  let H : HeadPreparation X := ⟨m+F.arity,X,Map.id X,specialRelative_id X 0,
    F.horizontal_translation_swapped_head_saturated hBalanced hNames⟩
  obtain ⟨r,D,T,hT,hD⟩ := gamma_unary_pullback_preparation_over_common_names C hNames γ hγ hγ1
    H.contractedSet (gamma_headImage X hX)
  let P := OrderedContractionProgram.step H (unarySpecialContractionProgram T hD)
  have hP : GammaProgramDefinable G P :=
    ⟨gamma_identity_graph X hX,hX,gamma_unary_special_contraction_program T hD hT⟩
  exact ⟨standardFromProgram Y (Equiv.swap 0 1) P rfl,
    gamma_standardFromProgram Y _ P rfl hP⟩

end IntegrationInACVF.Section7.UniformMixedCellPresentation
