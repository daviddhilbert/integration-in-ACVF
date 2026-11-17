module

public import Integration7.VolumeClassCoordinatePermutations
public import Integration7.SelectedVFTailPermutations
public import Integration7.SelectedStandardVolumeObjects
public import IntegrationSection6.StandardProgramPresentations

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The same ordered program on a permuted source restores two VF
coordinate conventions. Their selected tuples differ by precisely the
specified VF block permutation, and their retained densities agree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

def identityContractionOnPermutedSource {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
    (T : StandardContraction A σ) : StandardContraction (vfPermutationImage A σ) (Equiv.refl _) :=
  standardFromProgram (vfPermutationImage A σ) (Equiv.refl _) T.program
    (vfPermutationImage_id_eq (vfPermutationImage A σ)).symm

theorem identity_contraction_permuted_source_volume
    {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)} (T : StandardContraction A σ) (i : Fin n) :
    (identityContractionOnPermutedSource T).volumeIndex i = T.volumeIndex (σ i) := by
  change (orderedCastSource T.program _).volumeIndex i = T.program.volumeIndex (σ.symm (σ i))
  rw [orderedCastSource_volumeIndex,σ.symm_apply_apply]

theorem selected_permuted_source_volume_index
    {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)} (T : StandardContraction A σ)
    (ρ : Fin d → Fin a) :
    selectedStandardVolumeIndex (identityContractionOnPermutedSource T) ρ =
      selectedStandardVolumeIndex T ρ ∘ selectedVFTailPermutation d σ := by
  funext i
  obtain ⟨j,rfl⟩ := (finCongr (Nat.add_comm n d)).surjective i
  have hCast (j : Fin (n+d)) : finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) j) = j := Fin.ext rfl
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · change Fin.append (identityContractionOnPermutedSource T).volumeIndex _
      (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.castAdd d j))) = _
    rw [hCast,Fin.append_left]
    change _ = selectedStandardVolumeIndex T ρ
      (selectedVFTailPermutation d σ (finCongr (Nat.add_comm n d) (Fin.castAdd d j)))
    rw [selected_vf_tail_permutation_original]
    change _ = Fin.append T.volumeIndex _
      (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.castAdd d (σ j))))
    rw [hCast,Fin.append_left,identity_contraction_permuted_source_volume]
  · change Fin.append (identityContractionOnPermutedSource T).volumeIndex _
      (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.natAdd n j))) = _
    rw [hCast,Fin.append_right]
    change _ = selectedStandardVolumeIndex T ρ
      (selectedVFTailPermutation d σ (finCongr (Nat.add_comm n d) (Fin.natAdd n j)))
    rw [selected_vf_tail_permutation_tail]
    change _ = Fin.append T.volumeIndex _
      (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.natAdd n j)))
    rw [hCast,Fin.append_right]

def permutedNativeContractionVolumeIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (SpecialTransformations.Section3.Values.Gamma (M := M)))
    (A : DefSet (M := M) (C.base : Set M) (n+1) a) (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    RVVolumeIso ((selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).permuteVolume
      (selectedVFTailPermutation d σ))
      (selectedStandardVolumeObject hc C Ξ (vfPermutationImage A σ) ρ δ
        (vf_permuted_retained_density_nonzero A σ δ hδ) (vfPermutation_selected_finite A σ ρ hfin)
        (identityContractionOnPermutedSource T)) := by
  let U := (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T).permuteVolume (selectedVFTailPermutation d σ)
  let V := selectedStandardVolumeObject hc C Ξ (vfPermutationImage A σ) ρ δ
    (vf_permuted_retained_density_nonzero A σ δ hδ) (vfPermutation_selected_finite A σ ρ hfin)
    (identityContractionOnPermutedSource T)
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.id _
  have hCoord : ∀ u, V.underlying.obj.value (f u) = U.underlying.obj.value u := by
    intro u
    funext i
    exact congrArg u.val (congrFun (selected_permuted_source_volume_index T ρ) i)
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)

end IntegrationInACVF.Section7
