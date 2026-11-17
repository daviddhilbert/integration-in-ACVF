module

public import Integration7.VolumeFamilyCoproductRowMaps
public import Integration7.VolumeBlowupClasses

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Family disjoint union computes the genuine addition of RV volume
classes on every VF fibre, with the original coordinate maps and forms. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a b k : ℕ}

def volumeFamilyCoprodRowIso
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    RVVolumeIso ((F.coprod G).rowInContext x) ((F.rowInContext x).coprod (G.rowInContext x)) := by
  let D := vfParameterVolumeContext C x
  let U := (F.coprod G).rowInContext x
  let RF := F.rowInContext x
  let RG := G.rowInContext x
  let V := RF.coprod RG
  let f : Map V.underlying.obj.domain U.underlying.obj.domain :=
    Map.inclusion (fun r hr => (Set.ext_iff.mp (volume_family_coprod_row_carrier F G x) r).mpr hr)
  have hf : Function.Bijective f := by
    constructor
    · intro r s h
      have he := congrArg Subtype.val h
      exact Subtype.ext he
    · intro u
      exact ⟨⟨u.val,(Set.ext_iff.mp (volume_family_coprod_row_carrier F G x) u.val).mp u.property⟩,rfl⟩
  have hCoord : ∀ v, U.underlying.obj.value (f v) = V.underlying.obj.value v := by
    intro v
    rcases volumeCoprod_cases RF RG v with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have he : f (rvCoprodLeftMap RF.underlying.obj RG.underlying.obj r) = volumeFamilyCoprodRowLeftMap F G x r := Subtype.ext rfl
      rw [he]
      exact (volume_family_coprod_row_left_coordinates F G x r).trans (rvCoprod_value_left RF.underlying.obj RG.underlying.obj r).symm
    · have he : f (rvCoprodRightMap RF.underlying.obj RG.underlying.obj r) = volumeFamilyCoprodRowRightMap F G x r := Subtype.ext rfl
      rw [he]
      exact (volume_family_coprod_row_right_coordinates F G x r).trans (rvCoprod_value_right RF.underlying.obj RG.underlying.obj r).symm
  have hForm : ∀ v, U.form.value (f v) = V.form.value v := by
    intro v
    rcases volumeCoprod_cases RF RG v with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have he : f (rvCoprodLeftMap RF.underlying.obj RG.underlying.obj r) = volumeFamilyCoprodRowLeftMap F G x r := Subtype.ext rfl
      rw [he]
      exact (volume_family_coprod_row_left_density F G x r).trans (coprod_density_left RF RG r).symm
    · have he : f (rvCoprodRightMap RF.underlying.obj RG.underlying.obj r) = volumeFamilyCoprodRowRightMap F G x r := Subtype.ext rfl
      rw [he]
      exact (volume_family_coprod_row_right_density F G x r).trans (coprod_density_right RF RG r).symm
  exact (RVVolumeIso.of_preserving_coordinates_full hc D
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hCoord)) hCoord hForm).symm hc D

theorem volume_family_coprod_row_class
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : DefinableVFVolumeFamily C n a k) (G : DefinableVFVolumeFamily C n b k)
    (x : Fin n → VFType (M := M)) :
    positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) ((F.coprod G).rowInContext x) =
      positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (F.rowInContext x) +
        positiveVolumeBlowupClass hc (vfParameterVolumeContext C x) (G.rowInContext x) :=
  positiveVolumeBlowupClass_iso hc (vfParameterVolumeContext C x) (volumeFamilyCoprodRowIso hc F G x)

end IntegrationInACVF.Section7
