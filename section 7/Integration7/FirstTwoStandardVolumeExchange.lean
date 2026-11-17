module

public import Integration7.OrderedFirstTwoVolumeExchange
public import Integration7.GeometricFiniteStandardVolumeComparisons
public import Integration7.RetainedDensityContractionObjects
public import Integration7.SelectedVolumeCoordinatePermutations
public import Integration7.GammaPermutedSelectedVolumeFamilies
public import IntegrationSection6.PermutationFiniteFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Lemma7.7 in every VF arity: exchanging the first two coordinates of
the specified contraction order gives common forward original-Gamma
volume blowups. No Section5.8 input is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

set_option maxHeartbeats 3600000 in
theorem first_two_standard_volume_exchange
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hgamma : Cardinal.mk B.gamma < C.κ) (hGenerated : VFGammaGeneratedBase B)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hGeneric : ∀ {p : ℕ} (y : Fin p → VF (M := M)),
      AlgebraicIndependent (vfParameterField B.real) y →
        AlgebraicIndependent (vfParameterField (C.base : Set M)) y)
    (A : DefSet (M := M) (C.base : Set M) (n+2) a)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ y : Fin (n+2) → VF (M := M), {s : Fin a → RV (M := M) | (y,s) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ q : A, (q.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+2))}
    (T : StandardContraction A σ) (E : StandardContraction A ((swapFirstTwo n).trans σ))
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    let hsmall := (Cardinal.mk_le_mk_of_subset hBC).trans_lt C.small
    CommonContextVolumeEquivalent B C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC A hA hfin δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hsmall hc C hBC A hA hfin δ hδ E hE) := by
  intro hsmall
  have hδA : ∀ q ∈ carrier A, (q.2 δ).val ≠ iRVZero := fun q hq => hδ ⟨q,hq⟩
  have hδT := vf_permuted_retained_density_nonzero A σ δ hδA
  have hδE := vf_permuted_retained_density_nonzero A ((swapFirstTwo n).trans σ) δ hδA
  have hGeom := ordered_first_two_volume_exchange hc C hBC hNames hgamma hGenerated γ hγ hγ1 hGeneric
    (gamma_vfPermutationImage A hA σ) (vfPermutation_finite_rv_fibres A σ hfin)
    (vfPermutation_finite_rv_fibres A ((swapFirstTwo n).trans σ) hfin) δ
    (fun q => hδT q.val q.property) (fun q => hδE q.val q.property)
    (vfPrefix_permuted_swap A σ) T.program E.program hT hE
  have hδV := ordered_append_retained_density_nonzero T.program δ hδT
  have hδZ := ordered_append_retained_density_nonzero E.program δ hδE
  rw [ordered_append_density_index] at hδV hδZ
  have hPerm := selected_volume_geometry_permute hc T.target E.target
    (gamma_program_final_set T.program hT) (gamma_program_final_set E.program hE)
    T.program.volumeIndex (E.program.volumeIndex ∘ swapFirstTwo n)
    (suffixIndex T.program.rvArity_le δ) (suffixIndex E.program.rvArity_le δ)
    hδV hδZ (Fin.elim0 : Fin 0 → VF (M := M)) σ.symm hGeom
  have hTEq : T.program.volumeIndex ∘ σ.symm = T.volumeIndex := rfl
  have hEEq : (E.program.volumeIndex ∘ swapFirstTwo n) ∘ σ.symm = E.volumeIndex := by
    funext i
    change E.program.volumeIndex (swapFirstTwo n (σ.symm i)) =
      E.program.volumeIndex ((swapFirstTwo n).symm (σ.symm i))
    rw [show (swapFirstTwo n).symm = swapFirstTwo n from Equiv.symm_swap _ _]
  have hStandard : (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
      T.volumeIndex (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE)
        E.volumeIndex (suffixIndex E.program.rvArity_le δ))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
    simpa only [hTEq,hEEq] using hPerm
  exact finite_standard_volume_comparison_of_geometric_rows hc C C.uncountable.le C.saturated hsmall hBC
    A A hA hA hfin hfin T E hT hE δ δ hδ hδ hStandard

end IntegrationInACVF.Section7
