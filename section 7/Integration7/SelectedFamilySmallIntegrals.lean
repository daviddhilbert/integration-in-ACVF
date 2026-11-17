module

public import Integration7.SelectedCoordinateVolumeRealizations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A selected RV family supported on a smaller-dimensional VF domain
has zero integral. The proof uses its genuine full VF realization and
dimension invariance, with every retained density unchanged. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5 (VF RV carrier)
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

theorem raw_native_vf_arity_cast_dimension
    (hc : CanonicalStructure.IsCanonical (M := M)) {S : Set M} {p q a : ℕ} (h : p=q)
    (A : SpecialTransformations.Section5.DefSet (M := M) S p a) :
    vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc (nativeVFArityCast h A)) =
      vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) := by
  cases h
  rfl

theorem selected_coordinate_volume_realization_dimension_le
    (hc : CanonicalStructure.IsCanonical (M := M)) {C : BaseContext M}
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero) :
    vfDim (rawRVSpace (M := M) 1) (selectedCoordinateVolumeRealization hc A ρ hfin δ hδ).domain ≤
      vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) + d := by
  change vfDim (rawRVSpace (M := M) 1)
    (rawSpecialSet hc (nativeProgramSelectedRVVFTailLift hc A ρ)) ≤ _
  rw [nativeProgramSelectedRVVFTailLift,raw_native_vf_arity_cast_dimension]
  change vfDim (rawRVSpace (M := M) 1)
    (rawSpecialSet hc (nativeMixedVolumeDomain hc (selectedRVVFTailLift (rawSpecialSet hc A) ρ))) ≤ _
  rw [rawSpecialSet_nativeMixedVolumeDomain]
  exact selected_rv_vf_tail_lift_dim_le (rawSpecialSet hc A) ρ

theorem selected_standard_volume_integral_zero_of_small_domain
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hSmall : vfDim (rawRVSpace (M := M) 1) (rawSpecialSet hc A) < n+1)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    positiveVolumeBlowupClass hc C (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T) = 0 := by
  let W := selectedCoordinateVolumeRealization hc A ρ hfin δ hδ
  have hW : vfDim (rawRVSpace (M := M) 1) W.domain < (d+n)+1 :=
    (selected_coordinate_volume_realization_dimension_le hc A ρ hfin δ hδ).trans_lt (by omega)
  have hz := positiveVFVolumeIsoClass_small hc C W hW
  have hIntegral := selected_coordinate_volume_realization_integral hc C Ξ hΞ hGenerated hNames γ hγ hγ1
    A ρ hfin δ hδ T
  rw [hz] at hIntegral
  exact hIntegral.symm.trans (positive_volume_integration_zero hc C Ξ hΞ hGenerated hNames γ hγ hγ1)

end IntegrationInACVF.Section7
