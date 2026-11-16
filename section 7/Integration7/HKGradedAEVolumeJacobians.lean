module

public import Integration7.HKUnivSupportedVolumeEquivalences
public import Integration7.HKRawGradedChangeOfVariables
public import Integration7.PureVFPermutationDimensions

@[expose] public section

/-! Actual global VF Jacobian transforms act additively on every
homogeneous AE component and preserve the complete graded integral.
Coordinate permutations use this transform, including its determinant. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open scoped DirectSum

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

def aeVolumeComponentJacobianAddHom
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (j : ℕ) :
    AEVolumeFunctionComponent hc C n j →+ AEVolumeFunctionComponent hc C n j :=
  (supportedVolumeComponentForgetAddHom hc C _ j).comp
    ((supportedVolumeComponentJacobianAddHom hc C φ hφ j).comp
      (supportedVolumeComponentUnivEquiv hc C n j).symm.toAddMonoidHom)

def gradedAEVolumeJacobianAddHom
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) :
    GradedAEVolumeFunction hc C n →+ GradedAEVolumeFunction hc C n :=
  gradedComponentMapToSum (aeVolumeComponentJacobianAddHom hc C φ hφ)

theorem graded_ae_volume_jacobian_of
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (j : ℕ) (f : AEVolumeFunctionComponent hc C n j) :
    gradedAEVolumeJacobianAddHom hc C φ hφ (DirectSum.of _ j f) =
      DirectSum.of _ j (aeVolumeComponentJacobianAddHom hc C φ hφ j f) :=
  graded_component_map_to_sum_of _ j f

theorem pure_vf_univ_permutation_bijective (σ : Equiv.Perm (Fin (n+1))) :
    Function.Bijective (pureVFPermutationMap (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)) σ) := by
  constructor
  · intro x y h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change x.val ∘ σ = y.val ∘ σ at he
    funext i
    simpa only [Function.comp_apply,σ.apply_symm_apply] using congrFun he (σ.symm i)
  · intro y
    refine ⟨⟨y.val ∘ σ.symm,Set.mem_univ _⟩,Subtype.ext ?_⟩
    funext i
    exact congrArg y.val (σ.symm_apply_apply i)

def gradedAEVolumeCoordinatePermutationAddHom (σ : Equiv.Perm (Fin (n+1))) :
    GradedAEVolumeFunction hc C n →+ GradedAEVolumeFunction hc C n :=
  gradedAEVolumeJacobianAddHom hc C (pureVFPermutationMap (DefSet.univ _ _) σ)
    (pure_vf_univ_permutation_bijective C σ)

variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem ae_volume_component_jacobian_integral
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (j : ℕ) (f : AEVolumeFunctionComponent hc C n j) :
    aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j
      (aeVolumeComponentJacobianAddHom hc C φ hφ j f) =
    aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j f := by
  have h := supported_volume_component_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 φ hφ j
    ((supportedVolumeComponentUnivEquiv hc C n j).symm f)
  exact h.trans (congrArg (aeVolumeFunctionComponentIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n j)
    ((supportedVolumeComponentUnivEquiv hc C n j).apply_symm_apply f))

theorem graded_ae_volume_jacobian_integral
    (φ : Map (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M))
      (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)))
    (hφ : Function.Bijective φ) (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (gradedAEVolumeJacobianAddHom hc C φ hφ f) =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [graded_ae_volume_jacobian_of,graded_ae_volume_integral_of,graded_ae_volume_integral_of,
      ae_volume_component_jacobian_integral]

theorem graded_ae_volume_coordinate_permutation_integral (σ : Equiv.Perm (Fin (n+1)))
    (f : GradedAEVolumeFunction hc C n) :
    gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n
      (gradedAEVolumeCoordinatePermutationAddHom hc C σ f) =
      gradedAEVolumeIntegralAddHom hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f :=
  graded_ae_volume_jacobian_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ _ f

end IntegrationInACVF.Section7.HK
