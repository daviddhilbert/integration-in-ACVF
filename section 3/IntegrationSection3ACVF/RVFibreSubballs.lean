import IntegrationSection3ACVF.OpenBallRVGeometry
import IntegrationSection3ACVF.BallEnlargementGeometry

/-! A nonzero RV difference class is an actual open subball of any ball
containing its centre and the omitted point. No radius is named in a base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVFibreSubballs

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem exists_subball {A : Set M} (hA : IsBall A)
    (x y z : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hne : y ≠ x) (he : iRv (z-x).val = iRv (y-x).val) :
    ∃ i : BallImaginaries.Ball M,
      PaperBalls.IsOpenBall (BallImaginaries.underlying i) ∧
      BallImaginaries.underlying i ⊆ A ∧
      y.val ∈ BallImaginaries.underlying i ∧
      z.val ∈ BallImaginaries.underlying i ∧ x.val ∉ BallImaginaries.underlying i := by
  have hr0 : y-x ≠ 0 := sub_ne_zero.mpr hne
  have hγ : Values.vfValueHom (y-x) ≠ Values.infinity := by
    intro h
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp h
    exact hr0 ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (y-x),hγ⟩
  let P := gammaBall y γ true
  have hyP : y.val ∈ P := BallEnlargementGeometry.gammaBall_centre_mem y γ true
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hm (u : VFType (M := M)) : u.val ∈ P ↔ v (u-y) < v (y-x) :=
    GammaCosetGeometry.gammaBall_mem_valuation v hv y (y-x) γ rfl u
  have hxP : x.val ∉ P := by
    intro h
    have hl := (hm x).mp h
    have hn : v (x-y) = v (y-x) := by rw [← neg_sub y x,Valuation.map_neg]
    exact (lt_irrefl (v (y-x))) (hn ▸ hl)
  have hzP : z.val ∈ P := by
    apply (hm z).mpr
    have hc := (CanonicalRV.encoded_eq_iff_close (z-x).property (y-x).property
      (fun h => hr0 (Subtype.ext h))).mp he
    have hn : ¬ v (y-x) ≤ v ((z-x)-(y-x)) := fun h => hc ((hv _ _).mpr h)
    have hd : (z-x)-(y-x) = z-y := by ring
    rwa [hd,not_le] at hn
  have hPA : P ⊆ A := by
    rcases encodedBalls_laminar P (BallEnlargementGeometry.gammaBall_isBall y γ true) A hA
      with h | h | h
    · exact h
    · exact (hxP (h hx)).elim
    · exact (Set.disjoint_left.mp h hyP hy).elim
  obtain ⟨i,hi⟩ := GammaCosetGeometry.gammaBall_coded y γ
  exact ⟨i,Or.inr ⟨y,γ,hi⟩,hi.symm ▸ hPA,hi.symm ▸ hyP,hi.symm ▸ hzP,
    hi.symm ▸ hxP⟩

end IntegrationInACVF.Section3ACVF.RVFibreSubballs
