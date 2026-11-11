import IntegrationSection4.DefinableDescent
import Section5.VerticalConstruction

/-! Definable vertical coordinate changes with the complementary VF
coordinates fixed. These are actual maps and bijections; no preparation
existence is included in the structure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b c : ℕ}

structure RelativeBijection (A : DefSet (M := M) S (n+1) a)
    (B : DefSet (M := M) S (n+1) b) where
  toMap : Map A B
  bijective : Function.Bijective toMap
  tail : ∀ p : A, ∀ i : Fin n, vfAt (toMap p).val i.succ = vfAt p.val i.succ
  labels : ∀ p q : A, (toMap p).val.2 = (toMap q).val.2 → p.val.2 = q.val.2
  affine : ∀ p q : A, TailEq p.val q.val → (toMap p).val.2 = (toMap q).val.2 →
    vfAt (toMap p).val 0 - vfAt (toMap q).val 0 = vfAt p.val 0 - vfAt q.val 0
  inverse_rv : ∀ p q : A, SameRV (toMap p).val (toMap q).val → SameRV p.val q.val

namespace RelativeBijection

variable {A : DefSet (M := M) S (n+1) a} {B : DefSet (M := M) S (n+1) b}
variable {C : DefSet (M := M) S (n+1) c}

def inverseMap (T : RelativeBijection A B) : Map B A := Map.inverse T.toMap T.bijective

@[simp] theorem inverse_apply (T : RelativeBijection A B) (p : A) :
    T.inverseMap (T.toMap p) = p := Map.inverse_apply _ _ _

@[simp] theorem apply_inverse (T : RelativeBijection A B) (p : B) :
    T.toMap (T.inverseMap p) = p := Map.apply_inverse _ _ _

def refl (A : DefSet (M := M) S (n+1) a) : RelativeBijection A A where
  toMap := Map.id A
  bijective := Function.bijective_id
  tail _ _ := rfl
  labels _ _ h := h
  affine _ _ _ _ := rfl
  inverse_rv _ _ h := h

def comp (T : RelativeBijection A B) (U : RelativeBijection B C) : RelativeBijection A C where
  toMap := Map.comp U.toMap T.toMap
  bijective := U.bijective.comp T.bijective
  tail p i := (U.tail (T.toMap p) i).trans (T.tail p i)
  labels p q h := T.labels p q (U.labels (T.toMap p) (T.toMap q) h)
  affine p q ht hl := by
    have hTail : TailEq (T.toMap p).val (T.toMap q).val := fun i =>
      (T.tail p i).trans ((ht i).trans (T.tail q i).symm)
    exact (U.affine (T.toMap p) (T.toMap q) hTail hl).trans
      (T.affine p q ht (U.labels (T.toMap p) (T.toMap q) hl))
  inverse_rv p q h := T.inverse_rv p q (U.inverse_rv (T.toMap p) (T.toMap q) h)

def canonical (A : DefSet (M := M) S (n+1) a) : RelativeBijection A (canonicalImage A) where
  toMap := (SpecialBijection.canonical A).toMap
  bijective := (SpecialBijection.canonical A).bijective
  tail _ _ := rfl
  labels p q h := by
    funext i
    have hh := congrFun h (Fin.natAdd (n+1) i)
    change (SpecialTransformations.Section5.canonical p.val).2 (Fin.natAdd (n+1) i) =
      (SpecialTransformations.Section5.canonical q.val).2 (Fin.natAdd (n+1) i) at hh
    simpa only [canonical_old] using hh
  affine _ _ _ _ := rfl
  inverse_rv p q h := (canonical_sameRV_iff p.val q.val).mp h

theorem inverse_tail (T : RelativeBijection A B) (p : B) (i : Fin n) :
    vfAt (T.inverseMap p).val i.succ = vfAt p.val i.succ := by
  have h := T.tail (T.inverseMap p) i
  rw [T.apply_inverse] at h
  exact h.symm

theorem inverse_affine (T : RelativeBijection A B) (p q : B)
    (ht : TailEq p.val q.val) (hl : p.val.2 = q.val.2) :
    vfAt (T.inverseMap p).val 0 - vfAt (T.inverseMap q).val 0 = vfAt p.val 0 - vfAt q.val 0 := by
  have hTail : TailEq (T.inverseMap p).val (T.inverseMap q).val := fun i =>
    (T.inverse_tail p i).trans ((ht i).trans (T.inverse_tail q i).symm)
  have h := T.affine (T.inverseMap p) (T.inverseMap q) hTail
    (by rw [T.apply_inverse,T.apply_inverse]; exact hl)
  simpa only [T.apply_inverse] using h.symm

end RelativeBijection
end IntegrationInACVF.Section4
