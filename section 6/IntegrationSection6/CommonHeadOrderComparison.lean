import IntegrationSection6.ContractionOrderComparison
import IntegrationSection6.GammaHeadPermutationUniformity
import IntegrationSection6.StandardProgramPresentations
import IntegrationSection5.NaturalContractionGamma

/-! The induction step for two orders sharing their first coordinate.
The induction hypothesis is used only on the smaller VF arity. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}

theorem gamma_common_head_order_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (ih : ContractionOrderIndependent hκ.le hs h00 hreal n)
    (U : DefSet (M := M) Set.univ (n+1) a) (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (σ υ : Equiv.Perm (Fin (n+1))) (h0 : σ 0 = υ 0)
    (C : StandardContraction U σ) (E : StandardContraction U υ)
    (hC : GammaProgramDefinable B C.program) (hE : GammaProgramDefinable B E.program)
    (P : GammaSelectedRVPresentation B C.target (orderedSelectedIndex C.program ρ))
    (Q : GammaSelectedRVPresentation B E.target (orderedSelectedIndex E.program ρ)) :
    GammaIsp hκ.le hs h00 hreal P.toGamma Q.toGamma := by
  obtain ⟨τ,hOrder⟩ := contractionOrders_common_head σ υ h0
  rcases C with ⟨l,V,TC⟩
  rcases E with ⟨r,Z,TE⟩
  cases TC with
  | step T tail =>
    cases TE with
    | step E etail =>
      have hA := gamma_headImage T.target hC.2.1
      have hF := head_selected_fibres_finite hκ.le hs hreal T hC.1 hC.2.1 ρ
        (vfPermutation_selected_finite U σ ρ hfin)
      have hG := head_selected_fibres_finite hκ.le hs hreal E hE.1 hE.2.1 ρ
        (vfPermutation_selected_finite U υ ρ hfin)
      obtain ⟨D,hD,_,_,_⟩ := standard_contraction_exists_with_natural_graph hs h00 B hreal FBase
        (Set.subset_univ _) T.contractedSet hA τ
      obtain ⟨R⟩ := gammaSelectedRVPresentation_exists D.target (gamma_program_final_set D.program hD)
        (orderedSelectedIndex D.program (headVolumeIndex T ρ))
        (ordered_selected_fibres_finite hκ.le hs hreal D.program hD (headVolumeIndex T ρ)
          (vfPermutation_selected_finite T.contractedSet τ (headVolumeIndex T ρ) hF))
      let hStart := (vfPermutationImage_id_eq T.contractedSet).symm
      let C0 := standardFromProgram T.contractedSet (Equiv.refl _) tail hStart
      have hC0 := gamma_standardFromProgram T.contractedSet (Equiv.refl _) tail hStart hC.2.2
      have hIdx : orderedSelectedIndex C0.program (headVolumeIndex T ρ) =
          orderedSelectedIndex tail (headVolumeIndex T ρ) := standardFromProgram_selectedIndex _ _ _ _ _
      let P0 : GammaSelectedRVPresentation B C0.target (orderedSelectedIndex C0.program (headVolumeIndex T ρ)) :=
        P.congrFormula rfl (fun s y => and_congr Iff.rfl
          (Iff.of_eq (congrArg (fun θ => s ∘ θ = y) hIdx.symm)))
      have H0 := ih T.contractedSet hA (headVolumeIndex T ρ) hF (Equiv.refl _) τ C0 D hC0 hD P0 R
      have H1 : GammaIsp hκ.le hs h00 hreal P.toGamma R.toGamma := by
        simpa only [P0,GammaFiniteGraphPresentation.congrFormula_toGamma] using H0
      have H2 : GammaIsp hκ.le hs h00 hreal R.toGamma Q.toGamma := by
        apply lemma_6_14_ordered hκ hs h00 hreal hgamma δ hδ hδ1
          (vfPermutationImage T.contractedSet τ) E.contractedSet
          (gamma_vfPermutationImage T.contractedSet hA τ) (gamma_headImage E.target hE.2.1)
          (headVolumeIndex T ρ) (headVolumeIndex E ρ)
          (vfPermutation_selected_finite T.contractedSet τ (headVolumeIndex T ρ) hF) hG
          _ D.program etail hD hE.2.2 R Q
        intro x LP LQ
        apply gamma_head_permutation_uniformity hκ hs h00 hreal hgamma δ hδ hδ1
          T E hC.1 hE.1 hC.2.1 hE.2.1 ρ τ _ x LP LQ
        intro y
        rw [hOrder,← vfPermutationImage_trans]
        exact headTailFibre_carrier (vfPermutationImage U σ) τ y
      exact H1.trans H2

end IntegrationInACVF.Section6.FiniteRV
