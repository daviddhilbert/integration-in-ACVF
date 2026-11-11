import IntegrationSection3ACVF.AffineResidueSyntax

/-! The affine LRV graph has exactly the closed parent as its native VF
domain and exactly the actual residue coordinate as output. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section4.ResiduePurity
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

noncomputable section

namespace IntegrationInACVF.Section3ACVF.AffineResidueDomain

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem graph_iff_point (a r : VFType (M := M)) (α : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = α.val) (x : M) (t : ModelResidue M) :
    (![x,(residueRV t).val] : Fin 2 → M) ∈ AffineResidueSyntax.graph a r ↔
      ∃ p : BallResidueChart.Point a α, p.val.val = x ∧
        BallResidueChart.coordinate a r α hr p = t := by
  constructor
  · intro hg
    have hg0 := hg
    obtain ⟨u,hxu,hred⟩ := hg
    simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hxu hred
    have hle : Values.presentationValuation u ≤ 1 := by
      have hlow := hred.2.1
      have hp : VFValued.predV u 1 := by
        change iLe (iRv iVFOne) (iRv u.val)
        rwa [RVCalc.rv_one hM]
      simpa only [map_one] using (Values.presentation_compatible u 1).mp hp
    have hr0 := BallResidueChart.representative_ne_zero r α hr
    have he : (a+r*u-a)/r = u := by field_simp [hr0]; ring
    have hc : Values.presentationValuation (a+r*u-a) ≤ Values.presentationValuation r := by
      apply (AffineResidueChart.div_integral _ r hr0 _).mp
      rw [he]
      exact hle
    let p : BallResidueChart.Point a α := ⟨a+r*u,
      (BallKindPredicates.gammaBall_mem_valuation_closed Values.presentationValuation
        Values.presentation_compatible a r α hr (a+r*u)).mpr hc⟩
    have hpGraph : (![p.val.val,(residueRV t).val] : Fin 2 → M) ∈ AffineResidueSyntax.graph a r := by
      change (![(a+r*u).val,(residueRV t).val] : Fin 2 → M) ∈ AffineResidueSyntax.graph a r
      exact hxu ▸ hg0
    exact ⟨p,hxu.symm,((AffineResidueSyntax.coordinate_iff a r α hr p t).mp hpGraph).symm⟩
  · rintro ⟨p,hpx,hpt⟩
    have hg := (AffineResidueSyntax.coordinate_iff a r α hr p t).mpr hpt.symm
    exact hpx ▸ hg

end IntegrationInACVF.Section3ACVF.AffineResidueDomain
