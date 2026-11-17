module

public import Integration7.SelectedRVVFTailStandardContractions
public import Integration7.SelectedRVVFTailFullVolumeCoordinates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The extended standard contraction restores the original VF order.
Its literal RV projection retains that block and the old selected block. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a d r : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def selectedStandardVolumeIndex (T : StandardContraction A σ) (ρ : Fin d → Fin a) : Fin (d+n) → Fin T.arity :=
  Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ) ∘ finCongr (Nat.add_comm d n)

theorem selected_rv_vf_tail_standard_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (T : StandardContraction A σ)
    (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (v : V) :
    (canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E v).val.2 ∘
        selectedStandardVolumeIndex T ρ =
      v.val.2 ∘ (selectedRVVFTailStandardContraction hc T ρ E).volumeIndex := by
  funext i
  obtain ⟨j,rfl⟩ := (finCongr (Nat.add_comm n d)).surjective i
  have hcast (j : Fin (n+d)) : finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) j) = j := Fin.ext rfl
  refine Fin.addCases (fun i => ?_) (fun j => ?_) j
  · change (canonicalSelectedTailRVProjection hc T.target _ E v).val.2
      (Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ)
        (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.castAdd d i)))) = _
    rw [hcast,Fin.append_left]
    dsimp only [Function.comp_apply]
    rw [selected_rv_vf_tail_standard_volume_index,selected_vf_tail_permutation_symm_original]
    exact (selected_rv_vf_tail_full_original_volume hc T.program ρ E v (σ.symm i)).symm
  · change (canonicalSelectedTailRVProjection hc T.target _ E v).val.2
      (Fin.append T.volumeIndex (suffixIndex T.program.rvArity_le ∘ ρ)
        (finCongr (Nat.add_comm d n) (finCongr (Nat.add_comm n d) (Fin.natAdd n j)))) = _
    rw [hcast,Fin.append_right]
    dsimp only [Function.comp_apply]
    rw [selected_rv_vf_tail_standard_volume_index,selected_vf_tail_permutation_symm_tail]
    exact (selected_rv_vf_tail_full_selected_volume hc T.program ρ E hVF v j).symm

theorem selected_rv_vf_tail_standard_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (T : StandardContraction A σ)
    (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V) (v : V) (δ : Fin a) :
    (canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E v).val.2
      (suffixIndex T.program.rvArity_le δ) =
    v.val.2 (suffixIndex (selectedRVVFTailStandardContraction hc T ρ E).program.rvArity_le δ) :=
  (selected_rv_vf_tail_full_density hc T.program ρ E v δ).symm

end IntegrationInACVF.Section7
