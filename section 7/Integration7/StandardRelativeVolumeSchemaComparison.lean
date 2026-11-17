module

public import Integration7.OrderedRelativeVolumeSchemaComparison
public import Integration7.PermutedVFVolumeForms
public import Integration7.GammaPermutedSelectedVolumeFamilies
public import Integration7.SelectedVolumeCoordinatePermutations
public import Integration7.HeadTailVolumeSelectors
public import Integration7.GlobalRelativeVolumeContractions
public import Integration7.OrderedAppendVolumeFiniteness
public import Integration7.SelectedVolumeDegreeTransport
public import Integration7.GenericRelativeHeadVolumeComparison
public import Integration7.GenericOrderedAppendVolumeContractions
public import Integration7.RelativeHeadVolumeComparison
public import Integration7.OrderedAppendVolumeContractions

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Original global measure preservation is sufficient for comparison
of any specified head-first ordered contractions. Exceptional frozen
fibres are handled through the generic selected-volume induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b l r : ℕ}

set_option maxHeartbeats 2400000 in
theorem standard_relative_volume_schema_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hBase : B.real = (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {σ : Equiv.Perm (Fin (n+1))} (hi : UnaryRelative f (σ 0))
    (T : StandardContraction U σ) (E : StandardContraction V σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT) T.volumeIndex
      (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
    (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE) E.volumeIndex
      (suffixIndex E.program.rvArity_le ε)) (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  let Uσ := vfPermutationImage U σ
  let Vσ := vfPermutationImage V σ
  let g := vfPermutedMap f σ
  have hUσ := gamma_vfPermutationImage U hU σ
  have hVσ := gamma_vfPermutationImage V hV σ
  have hfinUσ : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier Uσ}.Finite := by
    intro x
    exact (hfinU (x ∘ σ.symm)).subset (fun r hr => (vfPermutationImage_row U σ x r).mp hr)
  have hfinVσ : ∀ x : Fin (n+1) → VF (M := M),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier Vσ}.Finite := by
    intro x
    exact (hfinV (x ∘ σ.symm)).subset (fun r hr => (vfPermutationImage_row V σ x r).mp hr)
  have h := ordered_relative_volume_schema_comparison hc C hκ hs hreal hgamma γ hγ hγ1 hBC hBase
    Uσ Vσ hUσ hVσ hfinUσ hfinVσ g (vfPermutedMap_bijective f hf σ)
    (gamma_vfPermutedMap f hU hV hfΓ σ) (vfPermutedMap_relative f σ hi)
    (permutedVFVolumeForm hc U ω σ) (permutedVFVolumeForm hc V π σ) δ ε
    (permuted_vf_volume_form_retained hc U ω σ δ hω)
    (permuted_vf_volume_form_retained hc V π σ ε hπ)
    (preserves_vf_volume_conjugate_permutation hc f σ ω π hm) T.program E.program hT hE
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans hz))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun hz => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans hz))
  have hδ' := ordered_append_retained_density_nonzero T.program δ (vf_permuted_retained_density_nonzero U σ δ hδ)
  have hε' := ordered_append_retained_density_nonzero E.program ε (vf_permuted_retained_density_nonzero V σ ε hε)
  rw [ordered_append_density_index] at hδ' hε'
  exact selected_volume_geometry_permute hc T.target E.target
    (gamma_program_final_set T.program hT) (gamma_program_final_set E.program hE)
    T.program.volumeIndex E.program.volumeIndex (suffixIndex T.program.rvArity_le δ)
    (suffixIndex E.program.rvArity_le ε) hδ' hε' (Fin.elim0 : Fin 0 → VF (M := M)) σ.symm h

end IntegrationInACVF.Section7
