import IntegrationSection3ACVF.PaperBalls
import IntegrationSection3ACVF.BallCodeGeometry
import IntegrationSection3ACVF.GammaCosetGeometry

/-! The sequel's open/closed predicates on the existing real ball charts.
Singletons are closed and VF is clopen. All radii are values of actual VF
elements; neither those elements nor the chart centres are base parameters. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.BallKindGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_raw_gammaBall (q : OpenBallCodes.Code M) (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom (⟨q.val 1,q.property.1 1⟩ : VFType (M := M)) = γ.val) :
    OpenBallCodes.rawBall q.val = gammaBall ⟨q.val 0,q.property.1 0⟩ γ true := by
  let a : VFType (M := M) := ⟨q.val 0,q.property.1 0⟩
  let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
  rw [← radiusBall_eq_gammaBall a (CanonicalRV.encodedRv r) γ hr true]
  ext x
  simp only [OpenBallCodes.rawBall,Set.mem_ofPred_eq,OpenBallCodes.body_realize,
    q.property,true_and]
  change (iVF x ∧ ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val)) ↔
    (iVF x ∧ iLe (iRv r.val) (iRv (iVFAdd x (iVFNeg a.val))) ∧
      (true = true → ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) (iRv r.val)))
  simp only [true_implies]
  constructor
  · rintro ⟨hx,hn⟩
    have hd : iRV (iRv (iVFAdd x (iVFNeg a.val))) :=
      rv_mem hM (vf_add_mem hM hx (vf_neg_mem hM a.property))
    rcases RVCalc.le_total_rv hM (rv_mem hM r.property) hd with h | h
    · exact ⟨hx,h,hn⟩
    · exact (hn h).elim
  · exact fun ⟨hx,_,hn⟩ => ⟨hx,hn⟩

theorem closed_raw_gammaBall (q : ClosedBallCodes.Code M) (hflag : q.val 2 ≠ iVFZero)
    (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom (⟨q.val 1,q.property 1⟩ : VFType (M := M)) = γ.val) :
    ClosedBallCodes.rawBall q.val = gammaBall ⟨q.val 0,q.property 0⟩ γ false := by
  let a : VFType (M := M) := ⟨q.val 0,q.property 0⟩
  let r : VFType (M := M) := ⟨q.val 1,q.property 1⟩
  rw [← radiusBall_eq_gammaBall a (CanonicalRV.encodedRv r) γ hr false]
  ext x
  simp only [ClosedBallCodes.rawBall,Set.mem_ofPred_eq,ClosedBallCodes.body_realize,
    hflag,false_or,and_iff_right q.property,radiusBall,Bool.false_eq_true,false_implies,and_true]

theorem open_raw_isOpenBall (q : OpenBallCodes.Code M) :
    PaperBalls.IsOpenBall (OpenBallCodes.rawBall q.val) := by
  let r : VFType (M := M) := ⟨q.val 1,q.property.1 1⟩
  have hr0 : r ≠ 0 := fun he => q.property.2 (congrArg Subtype.val he)
  have hr : Values.vfValueHom r ≠ Values.infinity := by
    intro he
    exact hr0 ((CanonicalRV.encodedRv_zero_iff r).mp
      ((Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv r)).mp he))
  exact Or.inr ⟨⟨q.val 0,q.property.1 0⟩,⟨Values.vfValueHom r,hr⟩,
    open_raw_gammaBall q _ rfl⟩

theorem closed_raw_isClosedBall (q : ClosedBallCodes.Code M) :
    PaperBalls.IsClosedBall (ClosedBallCodes.rawBall q.val) := by
  by_cases hflag : q.val 2 = iVFZero
  · left
    ext x
    simp only [ClosedBallCodes.rawBall,Set.mem_ofPred_eq,ClosedBallCodes.body_realize,
      hflag,true_or,and_true,and_iff_right q.property]
  · let a : VFType (M := M) := ⟨q.val 0,q.property 0⟩
    let r : VFType (M := M) := ⟨q.val 1,q.property 1⟩
    by_cases hr0 : r = 0
    · right; left
      refine ⟨a,?_⟩
      obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
      letI := hΓ
      have he : ClosedBallCodes.ball q.val = {a} := by
        have h := ClosedBallCodes.ball_eq_closed v hv q.val q.property hflag
        change ClosedBallCodes.ball q.val = ValOneEC.closedBall v a (v r) at h
        rw [hr0,map_zero,ValOneEC.closedBall_zero_radius] at h
        exact h
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
    · have hr : Values.vfValueHom r ≠ Values.infinity := by
        intro he
        exact hr0 ((CanonicalRV.encodedRv_zero_iff r).mp
          ((Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv r)).mp he))
      exact Or.inr (Or.inr ⟨a,⟨Values.vfValueHom r,hr⟩,closed_raw_gammaBall q hflag _ rfl⟩)

theorem gammaBall_open_code (a : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    ∃ q : OpenBallCodes.Code M, OpenBallCodes.rawBall q.val = gammaBall a γ true := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  have hr0 : r.val ≠ iVFZero := by
    intro he
    have hrz : r = 0 := Subtype.ext he
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [hrz,map_zero]; exact Values.infinity_eq_zero.symm
    exact γ.property (hr.symm.trans hz)
  let q : OpenBallCodes.Code M := ⟨![a.val,r.val],by
    refine ⟨?_,hr0⟩
    intro i
    fin_cases i
    · exact a.property
    · exact r.property⟩
  exact ⟨q,open_raw_gammaBall q γ hr⟩

theorem gammaBall_closed_code (a : VFType (M := M)) (γ : Values.Gamma (M := M)) :
    ∃ q : ClosedBallCodes.Code M, ClosedBallCodes.rawBall q.val = gammaBall a γ false := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  let q : ClosedBallCodes.Code M := ⟨![a.val,r.val,iVFOne],by
    intro i
    fin_cases i
    · exact a.property
    · exact r.property
    · exact (1 : VFType (M := M)).property⟩
  have hflag : q.val 2 ≠ iVFZero := by
    intro he
    exact (one_ne_zero : (1 : VFType (M := M)) ≠ 0) (Subtype.ext he)
  exact ⟨q,closed_raw_gammaBall q hflag γ hr⟩

end IntegrationInACVF.Section3ACVF.BallKindGeometry
