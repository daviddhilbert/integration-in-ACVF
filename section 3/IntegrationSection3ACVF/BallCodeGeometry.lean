import IntegrationSection3ACVF.BallPresentation

/-! The two directions between actual ball imaginaries and the unchanged
encoded ball point sets. The raw chart argument reuses the pinned
GeometryBridge.isKBall_vfImage proof, retaining its single-ball conclusion.
No code or centre is added to a parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.BallCodeGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem closed_raw_isBall (q : ClosedBallCodes.Code M) : IsBall (ClosedBallCodes.rawBall q.val) := by
  classical
  by_cases hflag : q.val 2 = iVFZero
  · left
    ext x
    change ((∀ i, iVF (q.val i)) ∧ iVF x ∧ ClosedBallCodes.body.Realize Fin.elim0
      (ClosedBallCodes.tuple q.val x)) ↔ iVF x
    rw [ClosedBallCodes.body_realize]
    exact ⟨fun h => h.2.1,fun hx => ⟨q.property,hx,Or.inl hflag⟩⟩
  · let a : VFType (M := M) := ⟨q.val 0,q.property 0⟩
    let r : VFType (M := M) := ⟨q.val 1,q.property 1⟩
    by_cases hr0 : r = 0
    · obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
      letI := hΓ
      have he : ClosedBallCodes.ball q.val = {a} := by
        simpa only [hr0,map_zero,ValOneEC.closedBall_zero_radius] using
          ClosedBallCodes.ball_eq_closed v hv q.val q.property hflag
      have hraw : ClosedBallCodes.rawBall q.val = {a.val} := by
        ext x
        constructor
        · intro hx
          let u : VFType (M := M) := ⟨x,hx.2.1⟩
          have hu : u ∈ ClosedBallCodes.ball q.val := hx
          rw [he] at hu
          exact congrArg Subtype.val (show u = a from hu)
        · intro hx
          have ha : a ∈ ClosedBallCodes.ball q.val := by rw [he]; exact Set.mem_singleton a
          exact (show x = a.val from hx).symm ▸ ha
      rw [hraw]
      right; right; right
      refine ⟨a.val,a.property,?_⟩
      ext x
      simp only [Set.mem_singleton_iff,Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h ▸ a.property,h⟩,fun h => h.2⟩
    · right; left
      refine ⟨a.val,iRv r.val,a.property,rv_mem hM r.property,?_,?_⟩
      · exact fun hz => hr0 ((CanonicalRV.encodedRv_zero_iff r).mp hz)
      · ext x
        simp only [ClosedBallCodes.rawBall,Set.mem_ofPred_eq,ClosedBallCodes.body_realize,
          q.property,true_and,hflag,false_or]
        rfl

theorem open_raw_isBall (q : OpenBallCodes.Code M) : IsBall (OpenBallCodes.rawBall q.val) := by
  let a : VFType (M := M) := ⟨q.val 0,q.property.1 0⟩
  let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
  have hr0 : r ≠ 0 := fun he => q.property.2 (congrArg Subtype.val he)
  right; right; left
  refine ⟨a.val,iRv r.val,a.property,rv_mem hM r.property,?_,?_⟩
  · exact fun hz => hr0 ((CanonicalRV.encodedRv_zero_iff r).mp hz)
  · ext x
    simp only [OpenBallCodes.rawBall,Set.mem_ofPred_eq,OpenBallCodes.body_realize,
      q.property,true_and]
    change (iVF x ∧ ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val)) ↔
      (iVF x ∧ iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))) ∧
        ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val))
    constructor
    · rintro ⟨hx,hn⟩
      have hd : iRV (iRv (iVFAdd x (iVFNeg a.val))) :=
        rv_mem hM (vf_add_mem hM hx (vf_neg_mem hM a.property))
      rcases RVCalc.le_total_rv hM (rv_mem hM r.property) hd with h | h
      · exact ⟨hx,h,hn⟩
      · exact (hn h).elim
    · exact fun ⟨hx,_,hn⟩ => ⟨hx,hn⟩

theorem underlying_isBall (i : BallImaginaries.Ball M) : IsBall (BallImaginaries.underlying i) := by
  obtain ⟨c,hc⟩ := Quotient.exists_rep i
  rw [← hc]
  cases c with
  | inl C =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep C
    rw [← hq]
    exact closed_raw_isBall q
  | inr O =>
    obtain ⟨q,hq⟩ := Quotient.exists_rep O
    rw [← hq]
    exact open_raw_isBall q

theorem encodedBall_coded (B : Set M) (hB : IsBall B) :
    ∃ i : BallImaginaries.Ball M, BallImaginaries.underlying i = B := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨i,hi⟩ := BallImaginaries.isBall_coded v hv B hB
  refine ⟨i,Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact (Set.ext_iff.mp hi (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M))).mpr hx
  · intro hx
    exact (Set.ext_iff.mp hi (⟨x,isBall_subset_vf B hB hx⟩ : VFType (M := M))).mp hx

end IntegrationInACVF.Section3ACVF.BallCodeGeometry
