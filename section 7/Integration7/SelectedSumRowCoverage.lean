module

public import Integration7.SelectedSumRowMaps

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every label of the actual selected sum comes from exactly one
of its two original summands; the individual maps are injective. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

theorem selected_sum_left_row_injective (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) : Function.Injective (selectedSumLeftRowMap F G x) := by
  intro r s h
  have hLabel := congrArg Subtype.val h
  rw [selected_sum_left_row_value,selected_sum_left_row_value] at hLabel
  have he : rvLeftTag b r.val = rvLeftTag b s.val := by
    funext i
    simpa only [Fin.append_left] using congrArg (fun t => t (Fin.castAdd (k+1) i)) hLabel
  exact Subtype.ext (rvLeftTag_injective b he)

theorem selected_sum_right_row_injective (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) : Function.Injective (selectedSumRightRowMap F G x) := by
  intro r s h
  have hLabel := congrArg Subtype.val h
  rw [selected_sum_right_row_value,selected_sum_right_row_value] at hLabel
  have he : rvRightTag a r.val = rvRightTag a s.val := by
    funext i
    simpa only [Fin.append_left] using congrArg (fun t => t (Fin.castAdd (k+1) i)) hLabel
  exact Subtype.ext (rvRightTag_injective a he)

theorem selected_sum_row_cover (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (q : ((selectedVolumeFamilySum F G).rowInContext x).underlying.obj.domain) :
    (∃ r, selectedSumLeftRowMap F G x r=q) ∨ (∃ r, selectedSumRightRowMap F G x r=q) := by
  let E := F.toDefinable.coprod G.toDefinable
  obtain ⟨r,hr⟩ := (E.selectionRowMap_bijective x).2 q
  let RF := F.toDefinable.rowInContext x
  let RG := G.toDefinable.rowInContext x
  let z : (RF.coprod RG).underlying.obj.domain :=
    ⟨r.val,(Set.ext_iff.mp (volume_family_coprod_row_carrier F.toDefinable G.toDefinable x) r.val).mp r.property⟩
  rcases volumeCoprod_cases RF RG z with ⟨u,hu⟩ | ⟨v,hv⟩
  · left
    have he : volumeFamilyCoprodRowLeftMap F.toDefinable G.toDefinable x u = r :=
      Subtype.ext (congrArg (fun w : (RF.coprod RG).underlying.obj.domain => w.val) hu)
    exact ⟨u,(congrArg (E.selectionRowMap x) he).trans hr⟩
  · right
    have he : volumeFamilyCoprodRowRightMap F.toDefinable G.toDefinable x v = r :=
      Subtype.ext (congrArg (fun w : (RF.coprod RG).underlying.obj.domain => w.val) hv)
    exact ⟨v,(congrArg (E.selectionRowMap x) he).trans hr⟩
end IntegrationInACVF.Section7
