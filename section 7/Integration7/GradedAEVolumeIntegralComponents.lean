import Integration7.GradedAEVolumeIntegralLinearMaps
import Integration7.GradedAEVolumeActionCoherence

/-! The assembled homogeneous integrals retain the genuine ordinary
integral and coefficient-first positive integrals, with arithmetic casts
only. Their values respect arithmetic homogeneous degree identification. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open scoped DirectSum

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_volume_component_integral_ordinary (n : ℕ) (f : AEOrdinaryRVVolumeFunction hc C n) :
    aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n 0 f =
      aeOrdinaryRVVolumeFunctionIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f := rfl

theorem ae_volume_component_integral_positive_heq (n k : ℕ) (f : AERVVolumeFunction hc C n k) :
    HEq (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n (k+1) f)
      (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f) := by
  have h : n+(k+1)=appendVolumeDegree (n+1) k := by rw [append_volume_degree_eq]; omega
  exact positive_volume_class_reindex_degree_heq hc C h
    (aeRVVolumeFunctionAppendedIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 f)

theorem ae_volume_component_integral_heq (n : ℕ) {i j : ℕ} (h : i=j)
    {f : AEVolumeFunctionComponent hc C n i} {g : AEVolumeFunctionComponent hc C n j} (hf : HEq f g) :
    HEq (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n i f)
      (aeVolumeFunctionComponentIntegralLinearMap hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j g) := by
  cases h
  cases hf
  rfl

theorem rv_volume_product_heq_of_inputs {i i' j j' : ℕ} (hi : i=i') (hj : j=j')
    {u : RVVolumeBlowupClasses hc C i} {v : RVVolumeBlowupClasses hc C i'}
    {f : RVVolumeBlowupClasses hc C j} {g : RVVolumeBlowupClasses hc C j'}
    (hu : HEq u v) (hf : HEq f g) :
    HEq (rvVolumeBlowupClassesProduct hc C i j u f) (rvVolumeBlowupClassesProduct hc C i' j' v g) := by
  cases hi
  cases hj
  cases hu
  cases hf
  rfl

end IntegrationInACVF.Section7
