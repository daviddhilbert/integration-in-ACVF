module

public import Integration7.AppendedFamilyFullLifts
public import Integration7.VFVolumeReindexingCoordinates

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Literal coordinates of the coefficient-first full family lift.
The front VF block realizes the selected RV tuple, and the remaining VF
block is the original family base; the old density is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k : ℕ}

def appendedFamilyBaseCoordinates (n k : ℕ)
    (x : Fin (appendVolumeDegree n k+1) → VFType (M := M)) : Fin n → VFType (M := M) :=
  x ∘ (finCongr (append_volume_length_eq n k)).symm ∘ Fin.natAdd (k+1)

def appendedFamilyCoefficientCoordinates (n k : ℕ)
    (x : Fin (appendVolumeDegree n k+1) → VFType (M := M)) : Fin (k+1) → VFType (M := M) :=
  x ∘ (finCongr (append_volume_length_eq n k)).symm ∘ Fin.castAdd n

theorem appended_family_lift_base_index (n k : ℕ) (i : Fin n) :
    appendedToOriginalVolumePermutation n k
      ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.castAdd (k+1) i)) =
      (finCongr (append_volume_length_eq n k)).symm (Fin.natAdd (k+1) i) := by
  change (finCongr (append_volume_length_eq n k)).symm
    ((finAddFlip : Fin (n+(k+1)) ≃ Fin ((k+1)+n))
      (finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n))
        ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.castAdd (k+1) i)))) = _
  have hi : finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n))
      ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.castAdd (k+1) i)) =
      Fin.castAdd (k+1) i := Fin.ext rfl
  rw [hi,finAddFlip_apply_castAdd]

theorem appended_family_lift_coefficient_index (n k : ℕ) (i : Fin (k+1)) :
    appendedToOriginalVolumePermutation n k
      ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.natAdd n i)) =
      (finCongr (append_volume_length_eq n k)).symm (Fin.castAdd n i) := by
  change (finCongr (append_volume_length_eq n k)).symm
    ((finAddFlip : Fin (n+(k+1)) ≃ Fin ((k+1)+n))
      (finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n))
        ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.natAdd n i)))) = _
  have hi : finCongr ((append_volume_length_eq n k).trans (Nat.add_comm (k+1) n))
      ((finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm (Fin.natAdd n i)) =
      Fin.natAdd n i := Fin.ext rfl
  rw [hi,finAddFlip_apply_natAdd]

theorem mem_appended_family_full_lift
    (F : SelectedVFVolumeFamily C n a k)
    (x : Fin (appendVolumeDegree n k+1) → VFType (M := M)) (r : Fin a → CanonicalRV.RVSort M) :
    (x,r) ∈ F.appendedFullLift.domain.carrier ↔
      (appendedFamilyBaseCoordinates n k x,r) ∈ F.domain.carrier ∧
        tupleRV (appendedFamilyCoefficientCoordinates n k x) = r ∘ F.selected := by
  change (x,r) ∈ (mixedVFPermutationDomain
    (F.fullLift.reindexDegree (appended_family_lift_degree_eq n k)).domain
      (appendedToOriginalVolumePermutation n k).symm).carrier ↔ _
  rw [mem_mixed_vf_permutation_domain,mem_vf_volume_reindex_degree]
  change (x ∘ (appendedToOriginalVolumePermutation n k).symm.symm ∘
    (finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm,r) ∈
      (selectedRVVFTailLift F.domain F.selected).carrier ↔ _
  rw [mem_selected_rv_vf_tail_lift]
  have hBase : (x ∘ (appendedToOriginalVolumePermutation n k).symm.symm ∘
      (finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm) ∘ Fin.castAdd (k+1) =
      appendedFamilyBaseCoordinates n k x := by
    funext i
    exact congrArg x (appended_family_lift_base_index n k i)
  have hCoefficient : (x ∘ (appendedToOriginalVolumePermutation n k).symm.symm ∘
      (finCongr (congrArg Nat.succ (appended_family_lift_degree_eq n k))).symm) ∘ Fin.natAdd n =
      appendedFamilyCoefficientCoordinates n k x := by
    funext i
    exact congrArg x (appended_family_lift_coefficient_index n k i)
  rw [hBase,hCoefficient]

theorem SelectedVFVolumeFamily.appendedFullLift_density
    (F : SelectedVFVolumeFamily C n a k) (q : F.appendedFullLift.domain) :
    F.appendedFullLift.form.value q = F.form.value
      ⟨(appendedFamilyBaseCoordinates n k q.val.1,q.val.2),
        ((mem_appended_family_full_lift F q.val.1 q.val.2).mp q.property).1⟩ := by
  let h := appended_family_lift_degree_eq n k
  let e := appendedToOriginalVolumePermutation n k
  let U := F.fullLift.reindexDegree h
  let p : U.domain := ⟨(q.val.1 ∘ e,q.val.2),
    (mem_mixed_vf_permutation_domain U.domain e.symm q.val.1 q.val.2).mp q.property⟩
  have hPerm := U.permuteVF_density e.symm q
  have hReindex := vf_volume_reindex_degree_density F.fullLift h p
  refine hPerm.trans (hReindex.trans ?_)
  apply congrArg F.form.value
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  funext i
  exact congrArg q.val.1 (appended_family_lift_base_index n k i)

end IntegrationInACVF.Section7
