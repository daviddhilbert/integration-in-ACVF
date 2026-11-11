import IntegrationSection5.RelativeInverseGeometry

/-! Exact ordinary-ball inverse slices of actual head preparations.
The ball calculation is adapted from the checked predecessor's
Section5.VerticalConstruction at the pinned revision; inverse affine
geometry here is proved from actual unary fibre special witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5.HeadPreparation
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S (n+1) m}

def inverseSlice (T : HeadPreparation A) (b : T.target) : Set (Point (M := M) (n+1) m) :=
  {p | ∃ a : A, a.val = p ∧ SameRV (T.map a).val b.val ∧ TailEq (T.map a).val b.val}

theorem inverse_pair (T : HeadPreparation A) (a b : T.target)
    (he : SameRV a.val b.val) (ht : TailEq a.val b.val) :
    TailEq (T.inverseMap a).val (T.inverseMap b).val ∧
      vfAt (T.inverseMap a).val 0-vfAt (T.inverseMap b).val 0 = vfAt a.val 0-vfAt b.val 0 := by
  refine ⟨?_,T.inverse_difference a b ht ((sameRV_iff _ _).mp he).2⟩
  intro j
  exact (T.inverse_tail a j).trans ((ht j).trans (T.inverse_tail b j).symm)

theorem inverse_slice {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VF (M := M)) Γ)
    (hv : ∀ x y : VF (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (T : HeadPreparation A) (b : T.target) (hb : vfAt b.val 0 ≠ 0) :
    T.inverseSlice b =
      {p | v (vfAt p 0 - vfAt (T.inverseMap b).val 0) < v (vfAt b.val 0) ∧
        TailEq p (T.inverseMap b).val ∧ p.2 = (T.inverseMap b).val.2} := by
  have hlabel (a c : T.target) (he : a.val.2 = c.val.2) :
      (T.inverseMap a).val.2 = (T.inverseMap c).val.2 := by
    exact T.inverse_labels a c he
  have hclose (x : VF (M := M)) :
      rv x = rv (vfAt b.val 0) ↔ v (x - vfAt b.val 0) < v (vfAt b.val 0) := by
    rw [Subtype.ext_iff]
    change iRv x.val = iRv (vfAt b.val 0).val ↔ _
    rw [CanonicalRV.encoded_eq_iff_close x.property (vfAt b.val 0).property
      (fun he => hb (Subtype.ext he))]
    change (¬ VFValued.predV (vfAt b.val 0) (x - vfAt b.val 0)) ↔ _
    rw [hv, not_le]
  ext p
  constructor
  · rintro ⟨a, rfl, he, ht⟩
    have hh := T.inverse_pair (T.map a) b he ht
    rw [T.inverse_apply] at hh
    have hl := hlabel (T.map a) b ((sameRV_iff _ _).mp he).2
    rw [T.inverse_apply] at hl
    refine ⟨?_, hh.1, hl⟩
    rw [hh.2]
    exact (hclose _).mp (((sameRV_iff _ _).mp he).1 0)
  · rintro ⟨hpv, hptail, hplabels⟩
    let q : Point (M := M) (n + 1) T.arity :=
      replace 0 b.val (vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0)
    have hq : SameRV q b.val := by
      apply (sameRV_replace 0 b.val _ ?_).symm
      apply (hclose _).mpr
      simpa only [add_sub_cancel_right] using hpv
    have htail : TailEq q b.val := by
      intro i
      simp [q, TailEq, vfAt, replace, Fin.succ_ne_zero]
    have hqB : q ∈ carrier T.target := T.saturated b.val b.property _ (((sameRV_iff _ _).mp hq).1 0)
    let c : T.target := ⟨q, hqB⟩
    have hh := T.inverse_pair c b hq htail
    have hc : (T.inverseMap c).val = p := by
      refine Prod.ext ?_ ((hlabel c b rfl).trans hplabels.symm)
      funext i
      cases i using Fin.cases with
      | zero =>
        have hd := hh.2
        change vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
          vfAt p 0 - vfAt (T.inverseMap b).val 0 + vfAt b.val 0 - vfAt b.val 0 at hd
        have hd' : vfAt (T.inverseMap c).val 0 - vfAt (T.inverseMap b).val 0 =
            vfAt p 0 - vfAt (T.inverseMap b).val 0 := by simpa only [add_sub_cancel_right] using hd
        have hevf : vfAt (T.inverseMap c).val 0 = vfAt p 0 := sub_left_inj.mp hd'
        exact hevf
      | succ i => exact (hh.1 i).trans (hptail i).symm
    exact ⟨T.inverseMap c, hc, by simpa only [T.apply_inverse] using hq,
      by simpa only [T.apply_inverse] using htail⟩

end IntegrationInACVF.Section5.HeadPreparation
