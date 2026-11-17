module

public import Integration7.PureVFPrefixImages
public import Integration7.VolumeCoordinateProjectionOrders

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The image used by permutation followed by a prefix integral is
exactly the image of the requested VF coordinate projection. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] {S : Set M} {n p : ℕ}

theorem volume_projection_prefix_slot (E : VFCoordinateProjection (n+1) (p+1))
    (i : Fin (p+1)) : vfPrefixRetainedIndex E.discarded p i = volumeProjectionRetainedSlot E i := by
  apply Fin.ext
  exact vf_prefix_retained_index_value E.discarded p i

theorem volume_projection_iterated_image
    (X : DefSet (rawVFSpace (M := M) (n+1)) S) (E : VFCoordinateProjection (n+1) (p+1)) :
    pureVFPrefixImage E.discarded p
      (pureVFCoordinateImage
        (pureVFCoordinateImage X (finCongr (congrArg Nat.succ (volume_projection_index_eq E))))
        (volumeProjectionFibreOrder E)) = pureVFCoordinateImage X E.retainedIndex := by
  rw [pure_vf_prefix_image_eq,pure_vf_coordinate_image_comp,pure_vf_coordinate_image_comp]
  congr 1
  funext i
  change finCongr (congrArg Nat.succ (volume_projection_index_eq E))
    (volumeProjectionFibreOrder E (vfPrefixRetainedIndex E.discarded p i)) = E.retainedIndex i
  rw [volume_projection_prefix_slot]
  exact volume_projection_order_retained E i
end IntegrationInACVF.Section7
