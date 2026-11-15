import Integration7.MatchingPreparedRVLabelCuts
import Integration7.StandardTargetRestrictionPresentations

/-! Every specified contraction of the whole pair-key refinement has
actual matching and different restrictions with unchanged target arity,
volume selectors and retained-label selectors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem matching_pair_contraction_presentation
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    {σ : Equiv.Perm (Fin 2)} (T : StandardContraction P.wholePreparedPairFamily σ)
    (hT : GammaProgramDefinable G T.program) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) T P.matchingPreparedFamily
      (rvLabelCut T.target (gamma_program_final_set T.program hT) (suffixIndex T.program.rvArity_le)
        P.matchingPreparedRVLabels P.matching_prepared_rv_labels_gamma hNames)) :=
  standard_label_cut_presentation_on_equal_source T P.whole_prepared_pair_family_gamma hT id
    P.matchingPreparedRVLabels P.matching_prepared_rv_labels_gamma hNames _ P.matching_prepared_eq_label_cut

theorem different_pair_contraction_presentation
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    {σ : Equiv.Perm (Fin 2)} (T : StandardContraction P.wholePreparedPairFamily σ)
    (hT : GammaProgramDefinable G T.program) :
    Nonempty (StandardTargetRestrictionPresentation (G := G) T P.differentPreparedFamily
      (rvLabelCut T.target (gamma_program_final_set T.program hT) (suffixIndex T.program.rvArity_le)
        P.differentPreparedRVLabels P.different_prepared_rv_labels_gamma hNames)) :=
  standard_label_cut_presentation_on_equal_source T P.whole_prepared_pair_family_gamma hT id
    P.differentPreparedRVLabels P.different_prepared_rv_labels_gamma hNames _ P.different_prepared_eq_label_cut

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
