module

public import IntegrationSection6.VFCoordinateProjections

@[expose] public section

/-! Put the discarded VF coordinates first and the retained coordinates
last, using the actual enumerations of a nonempty coordinate projection. -/
noncomputable section
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {n p : ℕ}

theorem volume_projection_index_eq (E : VFCoordinateProjection (n+1) (p+1)) : p+E.discarded=n := by
  have h := Fintype.card_congr E.split
  simp only [Fintype.card_fin] at h
  omega

def volumeProjectionFibreOrder (E : VFCoordinateProjection (n+1) (p+1)) :
    Equiv.Perm (Fin ((p+E.discarded)+1)) :=
  (finCongr (show (p+E.discarded)+1=E.discarded+(p+1) by omega)).trans
    ((finAddFlip : Fin (E.discarded+(p+1)) ≃ Fin ((p+1)+E.discarded)).trans
      (E.split.trans (finCongr (congrArg Nat.succ (volume_projection_index_eq E).symm))))

def volumeProjectionRetainedSlot (E : VFCoordinateProjection (n+1) (p+1))
    (j : Fin (p+1)) : Fin ((p+E.discarded)+1) :=
  Fin.cast (by omega) (Fin.natAdd E.discarded j)

theorem volume_projection_order_retained (E : VFCoordinateProjection (n+1) (p+1)) (j : Fin (p+1)) :
    finCongr (congrArg Nat.succ (volume_projection_index_eq E))
        (volumeProjectionFibreOrder E (volumeProjectionRetainedSlot E j)) = E.retainedIndex j := by
  unfold volumeProjectionFibreOrder volumeProjectionRetainedSlot
  simp only [Equiv.trans_apply]
  have hCast (z : Fin (n+1)) :
      finCongr (congrArg Nat.succ (volume_projection_index_eq E))
        (finCongr (congrArg Nat.succ (volume_projection_index_eq E).symm) z) = z := Fin.ext rfl
  rw [hCast]
  have hSlot : finCongr (show (p+E.discarded)+1=E.discarded+(p+1) by omega)
      (Fin.cast (by omega) (Fin.natAdd E.discarded j)) = Fin.natAdd E.discarded j := Fin.ext rfl
  rw [hSlot,finAddFlip_apply_natAdd]
  rfl

end IntegrationInACVF.Section7
