import Integration7.GradedAEVolumeIntegralCoefficientCompatibility

/-! Integration of the full actual graded AE function semimodule is
linear over the full graded common-blowup coefficient semiring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem graded_ae_volume_integral_smul
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ)
    (u : RVVolumeBlowupSemiring hc C) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (u • f) =
      u * gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  let I := gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
  induction u using DirectSum.induction_on with
  | zero => simp only [zero_smul,map_zero,zero_mul]
  | of i u =>
    induction f using DirectSum.induction_on with
    | zero => simp only [smul_zero,map_zero,mul_zero]
    | of j f =>
      rw [graded_ae_volume_coefficient_action_of,graded_ae_volume_integral_of,graded_ae_volume_integral_of,
        DirectSum.of_mul_of]
      exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (by change n+(i+j)+1=i+(n+j+1); omega)
        (ae_volume_component_integral_coefficient_heq hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n i j u f))
    | add f g hf hg =>
      change I (DirectSum.of (RVVolumeBlowupClasses hc C) i u • (f+g)) =
        DirectSum.of (RVVolumeBlowupClasses hc C) i u * I (f+g)
      calc
        _ = I (DirectSum.of (RVVolumeBlowupClasses hc C) i u • f) +
            I (DirectSum.of (RVVolumeBlowupClasses hc C) i u • g) := by rw [smul_add,map_add]
        _ = DirectSum.of (RVVolumeBlowupClasses hc C) i u * I f +
            DirectSum.of (RVVolumeBlowupClasses hc C) i u * I g := congrArg₂ (·+·) hf hg
        _ = _ := by rw [map_add,mul_add]
  | add u v hu hv =>
    change I ((u+v) • f)=(u+v)*I f
    calc
      _ = I (u • f)+I (v • f) := by rw [add_smul,map_add]
      _ = u*I f+v*I f := congrArg₂ (·+·) hu hv
      _ = _ := (add_mul u v (I f)).symm

def gradedAEVolumeIntegralLinearMap
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ) (n : ℕ) :
    GradedAEVolumeFunction hc C n →ₗ[RVVolumeBlowupSemiring hc C] RVVolumeBlowupSemiring hc C where
  toAddHom := (gradedAEVolumeIntegralOrdinaryLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n).toAddMonoidHom
  map_smul' u f := graded_ae_volume_integral_smul hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n u f

end IntegrationInACVF.Section7
