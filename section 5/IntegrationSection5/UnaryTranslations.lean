import IntegrationSection5.UnaryBallImages

/-! Actual translations of unary polydiscs, with all RV labels retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {m : ℕ}

def unaryShift (c : VF (M := M)) (p : Point (M := M) 1 m) : Point (M := M) 1 m :=
  (fun i => p.1 i - c, p.2)

theorem unaryShift_injective (c : VF (M := M)) : Function.Injective (unaryShift (m := m) c) := by
  intro p q he
  have hlabels := congrArg Prod.snd he
  refine Prod.ext ?_ hlabels
  funext i
  have hcoord := congrArg (fun p : Point (M := M) 1 m => p.1 i) he
  exact sub_left_inj.mp hcoord

theorem unaryShift_add_cancel (c : VF (M := M)) (p : Point (M := M) 1 m) :
    unaryShift c (fun i => p.1 i + c, p.2) = p := by
  refine Prod.ext ?_ rfl
  funext i
  exact add_sub_cancel_right _ _

theorem unaryShift_open_polydisc (c : VF (M := M)) {E : Set (Point (M := M) 1 m)}
    (hE : IsUnaryOpenPolydisc E) : IsUnaryOpenPolydisc (unaryShift c '' E) := by
  obtain ⟨a, r, hr, t, rfl⟩ := hE
  refine ⟨a - c, r, hr, t, ?_⟩
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩
    have he : (vfAt p 0 - c) - (a - c) = vfAt p 0 - a := by abel
    change (¬ iLe (rv ((vfAt p 0 - c) - (a - c))).val (rv r).val) ∧ p.2 = t
    rw [he]
    exact hp
  · intro hq
    let p : Point (M := M) 1 m := (fun i => q.1 i + c, q.2)
    refine ⟨p, ?_, unaryShift_add_cancel c q⟩
    have he : vfAt p 0 - a = vfAt q 0 - (a - c) := by
      change (q.1 0 + c) - a = q.1 0 - (a - c)
      abel
    change (¬ iLe (rv (vfAt p 0 - a)).val (rv r).val) ∧ q.2 = t
    rw [he]
    exact hq

theorem unaryShift_eq_zero_iff (c : VF (M := M)) (p : Point (M := M) 1 m) :
    vfAt (unaryShift c p) 0 = 0 ↔ vfAt p 0 = c := sub_eq_zero

end IntegrationInACVF.Section5
