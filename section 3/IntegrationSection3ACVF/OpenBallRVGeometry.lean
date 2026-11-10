import IntegrationSection3ACVF.PaperBalls
import IntegrationSection3ACVF.GammaCosetGeometry
import Section3.BallTranslation

/-! RV differences are constant on an actual open ball missing the
subtracted point. The sequel's singleton convention is retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OpenBallRVGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_sub_constant {Q : Set M} (hOpen : PaperBalls.IsOpenBall Q)
    (c x y : VFType (M := M)) (hc : c.val ∉ Q) (hx : x.val ∈ Q) (hy : y.val ∈ Q) :
    iRv (x-c).val = iRv (y-c).val := by
  rcases hOpen with hVF | ⟨a,α,he⟩
  · exact (hc (hVF.symm ▸ c.property)).elim
  · obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
    have hr0 : r ≠ 0 := by
      intro h
      have hz : Values.vfValueHom r = Values.infinity := by
        rw [h,map_zero]
        exact Values.infinity_eq_zero.symm
      exact α.property (hr.symm.trans hz)
    have hvr0 : v r ≠ 0 := (v.ne_zero_iff).mpr hr0
    let R : Balls.Radius Γ := ↑(OrderDual.toDual (v r))
    have hm (u : VFType (M := M)) : u.val ∈ Q ↔ u ∈ Balls.openDisc v a R := by
      rw [he]
      exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr u).trans
        (by simp [R,Balls.openDisc,hvr0])
    exact Balls.rv_sub_constant_openDisc v hv a c R
      (fun h => hc ((hm c).mpr h)) x y ((hm x).mp hx) ((hm y).mp hy)

end IntegrationInACVF.Section3ACVF.OpenBallRVGeometry
