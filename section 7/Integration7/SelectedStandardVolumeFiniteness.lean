module

public import Integration7.SelectedRVVFTailStandardVolumeCoordinates
public import Integration7.RawStandardVolumeFiniteness
public import Integration7.NativeSelectedVolumeFinitenessTransfer
public import Integration7.GammaSelectedRVVFTailPartialPrograms
public import Integration7.PositiveSelectedLemma75
public import Integration7.SelectedRVVFTailProgramCarriers

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Selected-volume finiteness for a standard contraction with its VF
coordinates in the original order. The proof uses the actual VF-tail
completion, rather than assuming a selected comparison theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d : ℕ}

theorem selected_standard_volume_fibres_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) n a) (ρ : Fin d → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin n)} (T : StandardContraction A σ) (t : Fin (d+n) → RV (M := M)) :
    {r : Fin T.arity → RV (M := M) |
      (Fin.elim0,r) ∈ carrier T.target ∧ r ∘ selectedStandardVolumeIndex T ρ = t}.Finite := by
  let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  have hT := gamma_program_over_real_base G T.program
  obtain ⟨r,V,E,hE,hVF,hCon,hFull⟩ := selected_rv_vf_tail_full_program_exists hc T.program
    (gamma_vfPermutationImage A hA σ) hT ρ
  let D := selectedRVVFTailStandardContraction hc T ρ E
  have hD : GammaProgramDefinable G D.program :=
    gamma_selected_rv_vf_tail_standard_contraction hc T ρ E hFull
  have hF := raw_standard_volume_fibres_finite C.uncountable.le C.saturated C.small
    (Set.Subset.refl _) (gamma_native_program_selected_rv_vf_tail_lift hc A ρ hA)
    (native_program_selected_rv_vf_tail_finite_labels hc A ρ hfin) D hD
  exact native_selected_volume_finiteness_transfer D.volumeIndex (selectedStandardVolumeIndex T ρ)
    (canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E)
    (canonical_selected_tail_rv_projection_bijective hc T.target _ E hCon).surjective
    (selected_rv_vf_tail_standard_volume hc T ρ E hVF) hF t

end IntegrationInACVF.Section7
