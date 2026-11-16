import Integration7.HKNormalizedPositiveOperators
import Integration7.PositiveGradedVolumeIntegration

/-! Actual positive-degree integrals agree under the additive transfer
of positive coefficient terms. Its zero-degree component is discarded;
this transfer is used only for integrals with positive total degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def positiveCoefficientTermsTransfer : Section7.RVVolumeBlowupSemiring hc C →+ RVVolumeBlowupSemiring hc C := by
  letI : ∀ d, AddCommMonoid (RVBlowupClasses hc C d) := rvVolumeBlowupClassesAddCommMonoid hc C
  exact DirectSum.toAddMonoid (fun j => match j with
    | 0 => 0
    | k+1 => DirectSum.of (RVBlowupClasses hc C) (k+1))

theorem positive_coefficient_terms_transfer_of (k : ℕ) (v : PositiveVolumeBlowupClasses hc C k) :
    positiveCoefficientTermsTransfer hc C (DirectSum.of (Section7.RVVolumeBlowupClasses hc C) (k+1) v) =
      DirectSum.of (RVBlowupClasses hc C) (k+1) v := by
  exact DirectSum.toAddMonoid_of (fun j => match j with
    | 0 => (0 : Section7.RVVolumeBlowupClasses hc C 0 →+ RVVolumeBlowupSemiring hc C)
    | l+1 => DirectSum.of (RVBlowupClasses hc C) (l+1)) (k+1) v

def positiveDegreeGradedInclusion (n : ℕ) :
    PositiveDegreeGradedVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] GradedAEVolumeFunction hc C n :=
  gradedShiftLinearEmbedding (aeVolumeFunctionGradedAction hc C n) 1

theorem positive_degree_graded_inclusion_of (n j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveDegreeGradedInclusion hc C n (DirectSum.of _ j f) =
      DirectSum.of (AEVolumeFunctionComponent hc C n) (j+1) f :=
  graded_shift_to_sum_of (F := AEVolumeFunctionComponent hc C n) 1 j f

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

def positiveDegreeGradedIntegral (n : ℕ) :
    PositiveDegreeGradedVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C :=
  (gradedAEVolumeIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).comp
    (positiveDegreeGradedInclusion hc C n)

theorem positive_degree_graded_integral_of (n j : ℕ) (f : AERVVolumeFunction hc C n j) :
    positiveDegreeGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (DirectSum.of _ j f) =
      DirectSum.of (RVBlowupClasses hc C) (appendVolumeDegree (n+1) j+1)
        (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  change gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
    (positiveDegreeGradedInclusion hc C n (DirectSum.of _ j f)) = _
  rw [positive_degree_graded_inclusion_of,graded_ae_volume_integral_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext
    (by change n+(j+1)+1=appendVolumeDegree (n+1) j+1; rw [append_volume_degree_eq]; omega)
    (ae_volume_component_integral_positive_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f))

theorem positive_degree_graded_integral_transfer (n : ℕ) (f : PositiveDegreeGradedVolumeFunction hc C n) :
    positiveDegreeGradedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f =
      positiveCoefficientTermsTransfer hc C
        (Section7.positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    have hOld := Section7.positive_graded_ae_volume_integral_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f
    have hNew := positive_degree_graded_integral_of hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f
    exact hNew.trans ((positive_coefficient_terms_transfer_of hc C _ _).symm.trans
      (congrArg (positiveCoefficientTermsTransfer hc C) hOld).symm)

end IntegrationInACVF.Section7.HK
