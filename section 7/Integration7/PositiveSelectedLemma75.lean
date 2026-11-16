module

public import Integration7.SelectedFamilyStandardVolumeComparison

@[expose] public section

/-! Lemma 7.5 for nonempty selected E: arbitrary actual standard
contractions in the same coordinate order preserve fibrewise common
volume blowups. The input is the ordinary common-blowup hypothesis on
the actual named VF fibres. All original selected coordinates and all
contracted VF tags are retained, together with the original density. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a b k : ℕ}

theorem gamma_program_over_real_base (B : Base (M := M))
    {n a l : ℕ} {U : DefSet (M := M) B.real n a} {V : DefSet (M := M) B.real 0 l}
    (T : OrderedContractionProgram B.real U V) : GammaProgramDefinable B T := by
  induction T with
  | zero U => exact (gammaLogicInput B).real_set _ (setDefinable U)
  | step T tail ih =>
    exact ⟨(gammaLogicInput B).real_map_graph T.map,
      (gammaLogicInput B).real_set _ (setDefinable T.target),ih⟩

set_option maxHeartbeats 2400000 in
theorem lemma_7_5_positive
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) σ) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    ∀ x : Fin 0 → VF (M := M),
      (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program (gamma_program_over_real_base B T.program))
        (orderedAppendVolumeIndex T.program F.densityGraph.selected) (orderedAppendDensityIndex T.program (Fin.last a))).commonByGammaGeometry
      (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program (gamma_program_over_real_base B E.program))
        (orderedAppendVolumeIndex E.program G.densityGraph.selected) (orderedAppendDensityIndex E.program (Fin.last b)))
      (fun j => (x j).val) := by
  intro B
  exact selected_family_standard_volume_comparison hc C Ξ hΞ γ hγ hγ1 F G hCommon T E
    (gamma_program_over_real_base B T.program) (gamma_program_over_real_base B E.program)

end IntegrationInACVF.Section7
