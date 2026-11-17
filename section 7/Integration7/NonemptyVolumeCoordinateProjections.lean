module

public import Integration7.VolumeCoordinateProjectionOrders

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Every nonempty coordinate subset gives a positive retained-arity
projection, retaining exactly the subset's actual coordinate indices. -/
noncomputable section
open Classical
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {n : ℕ}

theorem nonempty_coordinate_card_positive (E : Set (Fin (n+1))) (hE : E.Nonempty) : 0 < Fintype.card E := by
  obtain ⟨i,hi⟩ := hE
  letI : Nonempty E := ⟨⟨i,hi⟩⟩
  exact Fintype.card_pos

def nonemptyVolumeCoordinateProjection (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    VFCoordinateProjection (n+1) ((Fintype.card E).pred+1) where
  discarded := (VFCoordinateProjection.ofSet E).discarded
  split := (finCongr (congrArg (fun j => j+(VFCoordinateProjection.ofSet E).discarded)
    (Nat.succ_pred_eq_of_pos (nonempty_coordinate_card_positive E hE)))).trans (VFCoordinateProjection.ofSet E).split

theorem nonempty_volume_coordinate_projection_retained
    (E : Set (Fin (n+1))) (hE : E.Nonempty) (j : Fin ((Fintype.card E).pred+1)) :
    (nonemptyVolumeCoordinateProjection E hE).retainedIndex j =
      (VFCoordinateProjection.ofSet E).retainedIndex
        (finCongr (Nat.succ_pred_eq_of_pos (nonempty_coordinate_card_positive E hE)) j) := by
  change (VFCoordinateProjection.ofSet E).split _ = (VFCoordinateProjection.ofSet E).split _
  apply congrArg (VFCoordinateProjection.ofSet E).split
  exact Fin.ext rfl

theorem nonempty_volume_coordinate_projection_range
    (E : Set (Fin (n+1))) (hE : E.Nonempty) :
    Set.range (nonemptyVolumeCoordinateProjection E hE).retainedIndex = E := by
  ext i
  constructor
  · rintro ⟨j,rfl⟩
    apply (Set.ext_iff.mp (VFCoordinateProjection.ofSet_range E) _).mp
    exact ⟨_,(nonempty_volume_coordinate_projection_retained E hE j).symm⟩
  · intro hi
    obtain ⟨j,hj⟩ := (Set.ext_iff.mp (VFCoordinateProjection.ofSet_range E) i).mpr hi
    obtain ⟨q,hq⟩ := (finCongr (Nat.succ_pred_eq_of_pos (nonempty_coordinate_card_positive E hE))).surjective j
    exact ⟨q,(nonempty_volume_coordinate_projection_retained E hE q).trans ((congrArg _ hq).trans hj)⟩

end IntegrationInACVF.Section7
