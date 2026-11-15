import Integration7.UniformPreparedPositionRawGammaProducts

/-! The selected balanced part has actual compatible original-Gamma
preparations and the complete Gamma product equation, with nonzero
paradigms proved from the partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

theorem selected_balanced_position_preparation_exists (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A)) :
    Nonempty (UniformBalancedPositionPreparation G C (F.balancedNativeChart hNames)
      (F.balanced_native_chart_rows hNames γ hγ1) hNames) :=
  uniform_balanced_position_preparation_exists C hGC hNames γ hγ hγ1
    (F.balancedNativeChart hNames) (F.balanced_native_chart_rows hNames γ hγ1)

theorem selected_balanced_raw_gamma_products (C : BaseContext M)
    (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (P : UniformBalancedPositionPreparation G C (F.balancedNativeChart hNames)
      (F.balanced_native_chart_rows hNames γ hγ1) hNames)
    (u : rvObjectDomain (pullbackObject P.source)) (hu : u.val (0 : Fin (1+P.sourceArity)) ≠ rv (0 : VF (M := M))) :
    let Q := F.balancedNativeChart hNames
    ∃ b : F.balancedNativeSource hNames, ∃ r : RV (M := M),
      u.val ∘ (Fin.natAdd 1 ∘ P.sourceOldLabelIndex) = Fin.append b.val.2 (Q.parameters.toFun b) ∧
      Cells.IsBalanced (mixedPairFibre Q.parameters b) (Q.localPosition b) r
        ((Q.vertical.projection b).val.2 Q.vertical.paradigm_index) ∧
      Values.vrv r*Values.vrv (show RV (M := M) from (P.rawMap u).val (0 : Fin (1+P.targetArity))) =
        Values.vrv (show RV (M := M) from u.val (0 : Fin (1+P.sourceArity)))*Values.vrv ((Q.vertical.projection b).val.2 Q.vertical.paradigm_index) :=
  P.raw_gamma_products (F.balanced_native_chart_paradigm_nonzero hNames) u hu

end IntegrationInACVF.Section7.UniformMixedCellPresentation
