import IntegrationSection3ACVF.OpenBallRVGeometry

/-! Distances between two points of an open ball are strictly smaller
than distances from an inside point to a point outside that ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.OpenBallSeparationGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem inside_value_lt_outside {Q : Set M} (ho : PaperBalls.IsOpenBall Q)
    (x y z : VFType (M := M)) (hx : x.val ∈ Q) (hy : y.val ∉ Q) (hz : z.val ∈ Q) :
    Values.vfValueHom (y-x) < Values.vfValueHom (z-x) := by
  rcases ho with h | ⟨a,γ,h⟩
  · exact (hy (h.symm ▸ y.property)).elim
  · rw [h] at hx hy hz
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
    have hxv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr x).mp hx
    have hzv := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr z).mp hz
    have hzx : v (z-x) < v r := by
      have he : (z-a)-(x-a) = z-x := by ring
      simpa only [he] using v.map_sub_lt hzv hxv
    have hyx : v r ≤ v (y-x) := by
      apply le_of_not_gt
      intro hl
      apply hy
      apply (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr y).mpr
      have he : y-a = (y-x)+(x-a) := by ring
      rw [he]
      exact v.map_add_lt hl hxv
    have hdist := lt_of_lt_of_le hzx hyx
    apply lt_iff_le_not_ge.mpr
    refine ⟨(Values.vf_pred_iff_gamma_le (z-x) (y-x)).mp ((hv _ _).mpr hdist.le),?_⟩
    intro he
    exact not_le_of_gt hdist ((hv _ _).mp ((Values.vf_pred_iff_gamma_le (y-x) (z-x)).mpr he))

end IntegrationInACVF.Section3ACVF.OpenBallSeparationGeometry
