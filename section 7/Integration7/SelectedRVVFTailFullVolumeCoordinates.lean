import Integration7.SelectedRVVFTailFullPrograms
import Integration7.SelectedRVVFTailPartialSelectors
import Integration7.PartialOrderedVolumeSelectors
import Integration7.CanonicalSelectedTailVolumeCoordinates

/-! The completed lifted contraction has exactly the original VF
volume coordinates followed by the selected old RV coordinates. Its
retained arbitrary density is unchanged by the actual RV projection. -/
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a l d r : ℕ}
variable {A : DefSet (M := M) S n a} {U : DefSet (M := M) S 0 l}
variable {V : DefSet (M := M) S 0 r}

theorem selected_rv_vf_tail_full_original_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (T : OrderedContractionProgram S A U) (ρ : Fin d → Fin a)
    (E : OrderedContractionProgram S
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) V)
    (v : V) (i : Fin n) :
    v.val.2 ((selectedRVVFTailFullProgram hc T ρ E).volumeIndex
      (finCongr (Nat.add_comm n d) (Fin.castAdd d i))) =
      (canonicalSelectedTailRVProjection hc U (suffixIndex T.rvArity_le ∘ ρ) E v).val.2 (T.volumeIndex i) := by
  change v.val.2 ((appendPartialOrderedProgram (selectedRVVFTailPartialProgram hc T ρ) E).volumeIndex _) = _
  rw [append_partial_ordered_old_volume_index,selected_rv_vf_tail_partial_volume_index]
  rfl

theorem selected_rv_vf_tail_full_selected_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (T : OrderedContractionProgram S A U) (ρ : Fin d → Fin a)
    (E : OrderedContractionProgram S
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (v : V) (j : Fin d) :
    v.val.2 ((selectedRVVFTailFullProgram hc T ρ E).volumeIndex
      (finCongr (Nat.add_comm n d) (Fin.natAdd n j))) =
      (canonicalSelectedTailRVProjection hc U (suffixIndex T.rvArity_le ∘ ρ) E v).val.2
        (suffixIndex T.rvArity_le (ρ j)) := by
  change v.val.2 ((appendPartialOrderedProgram (selectedRVVFTailPartialProgram hc T ρ) E).volumeIndex _) = _
  rw [append_partial_ordered_tail_volume_index]
  exact canonical_selected_tail_volume_coordinates hc U _ E hVF v j

theorem selected_rv_vf_tail_full_density
    (hc : CanonicalStructure.IsCanonical (M := M)) (T : OrderedContractionProgram S A U) (ρ : Fin d → Fin a)
    (E : OrderedContractionProgram S
      (nativeProgramSelectedRVVFTailLift (n := 0) (d := d) hc U (suffixIndex T.rvArity_le ∘ ρ)) V)
    (v : V) (δ : Fin a) :
    v.val.2 (suffixIndex (selectedRVVFTailFullProgram hc T ρ E).rvArity_le δ) =
      (canonicalSelectedTailRVProjection hc U (suffixIndex T.rvArity_le ∘ ρ) E v).val.2
        (suffixIndex T.rvArity_le δ) := by
  rw [canonical_selected_tail_rv_projection_labels]
  apply congrArg v.val.2
  apply Fin.ext
  have hT := T.rvArity_le
  have hE := E.rvArity_le
  change r-a+δ.val = r-l+(l-a+δ.val)
  omega

end IntegrationInACVF.Section7
