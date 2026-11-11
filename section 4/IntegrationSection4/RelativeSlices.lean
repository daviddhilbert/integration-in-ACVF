import IntegrationSection4.RelativeRootReduction

/-! Inverse vertical slices for actual relative bijections.
The geometric argument generalizes the checked inverse-slice argument in
Special transformations, Section5/VerticalConstruction.lean, at revision
9cc9760892092dd34cfad4a6dee655843c52f30c. Only head saturation is needed here.
No special-bijection or prepared-domain existence is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section4.RelativeBijection

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}

def inverseSlice (T : RelativeBijection A B) (b : B) : Set (Point (M := M) (n+1) m) :=
  {p | ∃ a : A, a.val = p ∧ SameRV (T.toMap a).val b.val ∧ TailEq (T.toMap a).val b.val}

theorem inverse_labels (T : RelativeBijection A B) (a b : B) (he : a.val.2 = b.val.2) :
    (T.inverseMap a).val.2 = (T.inverseMap b).val.2 := by
  apply T.labels
  rwa [T.apply_inverse,T.apply_inverse]

theorem inverse_pair (T : RelativeBijection A B) (a b : B)
    (he : SameRV a.val b.val) (ht : TailEq a.val b.val) :
    TailEq (T.inverseMap a).val (T.inverseMap b).val ∧
      vfAt (T.inverseMap a).val 0-vfAt (T.inverseMap b).val 0 = vfAt a.val 0-vfAt b.val 0 :=
  ⟨fun i => (T.inverse_tail a i).trans ((ht i).trans (T.inverse_tail b i).symm),
    T.inverse_affine a b ht ((sameRV_iff _ _).mp he).2⟩

theorem inverse_slice {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (T : RelativeBijection A B) (hB : HeadSaturated (carrier B)) (b : B)
    (hb : vfAt b.val 0 ≠ 0) :
    T.inverseSlice b = {p | v (vfAt p 0-vfAt (T.inverseMap b).val 0) < v (vfAt b.val 0) ∧
      TailEq p (T.inverseMap b).val ∧ p.2 = (T.inverseMap b).val.2} ∧
      T.inverseSlice b ⊆ {p | SameRV p (T.inverseMap b).val} := by
  have hclose (x : VF (M := M)) : rv x = rv (vfAt b.val 0) ↔
      v (x-vfAt b.val 0) < v (vfAt b.val 0) := by
    rw [Subtype.ext_iff]
    change iRv x.val = iRv (vfAt b.val 0).val ↔ _
    rw [CanonicalRV.encoded_eq_iff_close x.property (vfAt b.val 0).property (fun he => hb (Subtype.ext he))]
    change (¬ VFValued.predV (vfAt b.val 0) (x-vfAt b.val 0)) ↔ _
    rw [hv,not_le]
  constructor
  · ext p
    constructor
    · rintro ⟨a,rfl,he,ht⟩
      have hh := T.inverse_pair (T.toMap a) b he ht
      rw [T.inverse_apply] at hh
      refine ⟨?_,hh.1,?_⟩
      · rw [hh.2]
        exact (hclose _).mp (((sameRV_iff _ _).mp he).1 0)
      · have hl := T.inverse_labels (T.toMap a) b (((sameRV_iff _ _).mp he).2)
        simpa only [T.inverse_apply] using hl
    · rintro ⟨hpv,hptail,hplabels⟩
      let x := vfAt p 0-vfAt (T.inverseMap b).val 0+vfAt b.val 0
      have hx : rv x = rv (vfAt b.val 0) := (hclose x).mpr (by simpa only [x,add_sub_cancel_right] using hpv)
      let q : B := ⟨replace 0 b.val x,hB b.val b.property x hx⟩
      have hqRV : SameRV q.val b.val := (sameRV_replace 0 b.val x hx).symm
      have hqTail : TailEq q.val b.val := by intro i; simp [q,replace,vfAt,Fin.succ_ne_zero]
      have hh := T.inverse_pair q b hqRV hqTail
      have hqp : (T.inverseMap q).val = p := by
        apply Prod.ext
        · funext i
          cases i using Fin.cases with
          | zero =>
            have hd := hh.2
            change vfAt (T.inverseMap q).val 0-vfAt (T.inverseMap b).val 0 =
              x-vfAt b.val 0 at hd
            dsimp only [x] at hd
            rw [add_sub_cancel_right] at hd
            have hd' : vfAt (T.inverseMap q).val 0 = vfAt p 0 := sub_left_inj.mp hd
            exact hd'
          | succ i => exact (hh.1 i).trans (hptail i).symm
        · exact (T.inverse_labels q b rfl).trans hplabels.symm
      exact ⟨T.inverseMap q,hqp,by simpa only [T.apply_inverse] using hqRV,
        by simpa only [T.apply_inverse] using hqTail⟩
  · rintro p ⟨a,rfl,he,_⟩
    apply T.inverse_rv a (T.inverseMap b)
    simpa only [T.apply_inverse] using he

end IntegrationInACVF.Section4.RelativeBijection
