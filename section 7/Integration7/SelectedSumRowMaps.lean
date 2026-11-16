module

public import Integration7.SelectedVolumeFamilyAddition

@[expose] public section

/-! The two original families embed in their actual selected sum on
each named VF row, retaining both coordinates and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def selectedSumLeftRowMap (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    Map (F.rowInContext x).underlying.obj.domain ((selectedVolumeFamilySum F G).rowInContext x).underlying.obj.domain :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap x).comp
    (volumeFamilyCoprodRowLeftMap F.toDefinable G.toDefinable x)

def selectedSumRightRowMap (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    Map (G.rowInContext x).underlying.obj.domain ((selectedVolumeFamilySum F G).rowInContext x).underlying.obj.domain :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap x).comp
    (volumeFamilyCoprodRowRightMap F.toDefinable G.toDefinable x)

theorem selected_sum_left_row_value (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    (selectedSumLeftRowMap F G x r).val =
      Fin.append (rvLeftTag b r.val) ((F.rowInContext x).underlying.obj.value r) := by
  change ((F.toDefinable.coprod G.toDefinable).selectionRowMap x
    (volumeFamilyCoprodRowLeftMap F.toDefinable G.toDefinable x r)).val = _
  rw [DefinableVFVolumeFamily.selectionRowMap_value,volume_family_coprod_row_left_coordinates]
  rfl

theorem selected_sum_right_row_value (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    (selectedSumRightRowMap F G x r).val =
      Fin.append (rvRightTag a r.val) ((G.rowInContext x).underlying.obj.value r) := by
  change ((F.toDefinable.coprod G.toDefinable).selectionRowMap x
    (volumeFamilyCoprodRowRightMap F.toDefinable G.toDefinable x r)).val = _
  rw [DefinableVFVolumeFamily.selectionRowMap_value,volume_family_coprod_row_right_coordinates]
  rfl

theorem selected_sum_left_row_coordinates (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    ((selectedVolumeFamilySum F G).rowInContext x).underlying.obj.value (selectedSumLeftRowMap F G x r) =
      (F.rowInContext x).underlying.obj.value r :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap_coordinates x _).trans
    (volume_family_coprod_row_left_coordinates F.toDefinable G.toDefinable x r)

theorem selected_sum_right_row_coordinates (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    ((selectedVolumeFamilySum F G).rowInContext x).underlying.obj.value (selectedSumRightRowMap F G x r) =
      (G.rowInContext x).underlying.obj.value r :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap_coordinates x _).trans
    (volume_family_coprod_row_right_coordinates F.toDefinable G.toDefinable x r)

theorem selected_sum_left_row_density (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (F.rowInContext x).underlying.obj.domain) :
    ((selectedVolumeFamilySum F G).rowInContext x).form.value (selectedSumLeftRowMap F G x r) =
      (F.rowInContext x).form.value r :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap_density x _).trans
    (volume_family_coprod_row_left_density F.toDefinable G.toDefinable x r)

theorem selected_sum_right_row_density (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) (r : (G.rowInContext x).underlying.obj.domain) :
    ((selectedVolumeFamilySum F G).rowInContext x).form.value (selectedSumRightRowMap F G x r) =
      (G.rowInContext x).form.value r :=
  ((F.toDefinable.coprod G.toDefinable).selectionRowMap_density x _).trans
    (volume_family_coprod_row_right_density F.toDefinable G.toDefinable x r)
end IntegrationInACVF.Section7
