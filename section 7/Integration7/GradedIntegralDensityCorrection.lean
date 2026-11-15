import Integration7.PositiveGradedVolumeFubini

/-! Density correction on graded integral values is additive. It is
only applied to positive total degrees; this construction does not
assign a volume form to ordinary RV[0] objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4.ResiduePurity
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (c : CanonicalRV.RVSort M) (hcS : c.val ∈ C.base) (hc0 : c ≠ 0)

def gradedVolumeDensityCorrection : RVVolumeBlowupSemiring hc C →+ RVVolumeBlowupSemiring hc C :=
  DirectSum.toAddMonoid (fun j => match j with
    | 0 => DirectSum.of (RVVolumeBlowupClasses hc C) 0
    | k+1 => (DirectSum.of (RVVolumeBlowupClasses hc C) (k+1)).comp
      (positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0))

theorem graded_volume_density_correction_positive_of (j : ℕ) (u : PositiveVolumeBlowupClasses hc C j) :
    gradedVolumeDensityCorrection hc C c hcS hc0 (DirectSum.of (RVVolumeBlowupClasses hc C) (j+1) u) =
      DirectSum.of (RVVolumeBlowupClasses hc C) (j+1)
        (positiveVolumeClassRescaleDefinable hc C c (Set.Definable.singleton_of_mem LRV hcS) hc0 u) := by
  apply DirectSum.toAddMonoid_of

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem positive_graded_integral_density_correction (n : ℕ) (f : PositiveGradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (positiveGradedAEVolumeDensityRescale hc C c hcS hc0 n f) =
    gradedVolumeDensityCorrection hc C c hcS hc0
      (positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [positive_graded_density_rescale_of,positive_graded_ae_volume_integral_of,
      positive_graded_ae_volume_integral_of,graded_volume_density_correction_positive_of,
      ae_rv_volume_appended_integral_density_rescale]

omit c hcS hc0 in
theorem ae_volume_component_integral_signed_permutation (n j : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : AEVolumeFunctionComponent hc C n j) :
    positiveVolumeClassRescaleDefinable hc C (rvPermutationSign σ)⁻¹
      (Set.Definable.singleton_of_mem LRV (rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)))
      (inv_ne_zero (rvPermutationSign_ne_zero σ))
      (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
        (aeVolumeFunctionComponentPermutationLinearMap hc C n σ j f)) =
      aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f := by
  cases j with
  | zero => exact ae_ordinary_volume_integral_signed_permutation hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f σ
  | succ k =>
    have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
    have hL := dependent_degree_map_heq
      (fun q => positiveVolumeClassRescaleDefinable (k := q) hc C (rvPermutationSign σ)⁻¹
        (Set.Definable.singleton_of_mem LRV (rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)))
        (inv_ne_zero (rvPermutationSign_ne_zero σ))) h
      (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k
        (aeRVVolumeFunctionPermuteBase hc C σ f))
    exact eq_of_heq (hL.trans
      ((heq_of_eq (ae_rv_volume_appended_integral_signed_permutation hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f σ)).trans
        (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n k f).symm))

omit c hcS hc0 in
theorem graded_ae_volume_integral_signed_permutation (n : ℕ) (σ : Equiv.Perm (Fin (n+1)))
    (f : GradedAEVolumeFunction hc C n) :
    gradedVolumeDensityCorrection hc C (rvPermutationSign σ)⁻¹
      (rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ)) (inv_ne_zero (rvPermutationSign_ne_zero σ))
      (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (gradedAEVolumePermutationLinearMap hc C n σ f)) =
      gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    change gradedVolumeDensityCorrection hc C _ _ _
      (gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
        (gradedAEVolumePermutationLinearMap hc C n σ (DirectSum.of _ j f))) =
      gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (DirectSum.of _ j f)
    rw [graded_ae_volume_permutation_of,graded_ae_volume_integral_of,graded_ae_volume_integral_of,
      graded_volume_density_correction_positive_of,ae_volume_component_integral_signed_permutation]
end IntegrationInACVF.Section7
