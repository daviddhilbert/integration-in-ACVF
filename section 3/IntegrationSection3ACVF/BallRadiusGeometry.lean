import IntegrationSection3ACVF.BallKindPredicates
import IntegrationSection3ACVF.CanonicalBallSupport
import IntegrationSection3.ValuationRadius

/-! Uniqueness of ordinary Gamma radii and separation of open and closed
balls. The valuation-density input is supplied by the existing ACVF-QE
proof, with nontriviality derived from an actual Gamma value above one. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open ValOneEC
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.BallRadiusGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem valuation_dense {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ) :
    ∀ r s : VFType (M := M), v r < v s → ∃ t, v r < v t ∧ v t < v s := by
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  have hnt := (Johnson.exists_ne_zero_val_lt_one_iff v).mpr
    (CanonicalBallSupport.valuation_nontrivial v hv δ hδ)
  exact fun _ _ h => Johnson.exists_val_between' v hnt h

theorem gamma_radius_unique_same_kind (a b : VFType (M := M))
    (α β : Values.Gamma (M := M)) (strict : Bool)
    (he : gammaBall a α strict = gammaBall b β strict) : α = β := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative β
  have hvr : v r = v s := by
    cases strict with
    | false =>
      have hn : {x : VFType (M := M) | v (x-a) ≤ v r} = {x | v (x-b) ≤ v s} := by
        ext x
        exact (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr x).symm.trans
          ((Set.ext_iff.mp he x.val).trans
            (BallKindPredicates.gammaBall_mem_valuation_closed v hv b s β hs x))
      exact le_antisymm
        (ValuationRadius.closed_radius_le_of_subset v a b r s hn.subset)
        (ValuationRadius.closed_radius_le_of_subset v b a s r hn.symm.subset)
    | true =>
      have hn : {x : VFType (M := M) | v (x-a) < v r} = {x | v (x-b) < v s} := by
        ext x
        exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).symm.trans
          ((Set.ext_iff.mp he x.val).trans
            (GammaCosetGeometry.gammaBall_mem_valuation v hv b s β hs x))
      have hr0 : r ≠ 0 := by
        intro h
        have hz : Values.vfValueHom r = Values.infinity := by
          rw [h,map_zero]; exact Values.infinity_eq_zero.symm
        exact α.property (hr.symm.trans hz)
      have hs0 : s ≠ 0 := by
        intro h
        have hz : Values.vfValueHom s = Values.infinity := by
          rw [h,map_zero]; exact Values.infinity_eq_zero.symm
        exact β.property (hs.symm.trans hz)
      exact Balls.strictDisc_radius_eq_of_eq v a b r s hr0 hs0 hn
  apply Subtype.ext
  exact hr.symm.trans (((Values.vf_value_eq_iff v hv r s).mpr hvr).trans hs)

theorem gamma_open_ne_closed (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a b : VFType (M := M)) (α β : Values.Gamma (M := M)) :
    gammaBall a α true ≠ gammaBall b β false := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  obtain ⟨s,hs⟩ := GammaCosetGeometry.vf_representative β
  have hr0 : r ≠ 0 := by
    intro h
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [h,map_zero]; exact Values.infinity_eq_zero.symm
    exact α.property (hr.symm.trans hz)
  intro he
  apply ValuationRadius.open_ne_closed v (valuation_dense v hv δ hδ) a b r s hr0
  ext x
  exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).symm.trans
    ((Set.ext_iff.mp he x.val).trans
      (BallKindPredicates.gammaBall_mem_valuation_closed v hv b s β hs x))

theorem gamma_open_not_closed (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    ¬ PaperBalls.IsClosedBall (gammaBall a α true) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hr0 : r ≠ 0 := by
    intro h
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [h,map_zero]; exact Values.infinity_eq_zero.symm
    exact α.property (hr.symm.trans hz)
  rintro (hVF | ⟨b,hpoint⟩ | ⟨b,β,hclosed⟩)
  · have hx : (a+r).val ∈ gammaBall a α true := by rw [hVF]; exact (a+r).property
    have hn := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr (a+r)).mp hx
    have hbad : v r < v r := by simpa only [add_sub_cancel_left] using hn
    exact lt_irrefl _ hbad
  · apply ValuationRadius.open_ne_closed v (valuation_dense v hv δ hδ) a b r 0 hr0
    ext x
    have he : x.val ∈ gammaBall a α true ↔ x = b := by
      rw [hpoint]
      exact ⟨Subtype.ext,congrArg Subtype.val⟩
    rw [← GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x,he]
    simp only [map_zero,le_zero_iff,map_eq_zero,sub_eq_zero]
  · exact gamma_open_ne_closed δ hδ a b α β hclosed

theorem open_closed_only_vf (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set M} (ho : PaperBalls.IsOpenBall D) (hc : PaperBalls.IsClosedBall D) :
    D = {x | iVF x} := by
  rcases ho with h | ⟨a,α,rfl⟩
  · exact h
  · exact (gamma_open_not_closed δ hδ a α hc).elim

theorem gammaBall_ne_vf (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (strict : Bool) :
    gammaBall a α strict ≠ {x | iVF x} := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hnt := (Johnson.exists_ne_zero_val_lt_one_iff v).mpr
    (CanonicalBallSupport.valuation_nontrivial v hv δ hδ)
  obtain ⟨z,_,hrz,_⟩ := Johnson.exists_val_gt_max v hnt r r
  intro he
  have hx : (a+z).val ∈ gammaBall a α strict := by rw [he]; exact (a+z).property
  cases strict with
  | false =>
    have hn := (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr (a+z)).mp hx
    have hbad : v z ≤ v r := by simpa only [add_sub_cancel_left] using hn
    exact not_le_of_gt hrz hbad
  | true =>
    have hn := (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr (a+z)).mp hx
    have hbad : v z < v r := by simpa only [add_sub_cancel_left] using hn
    exact not_lt_of_ge hrz.le hbad

theorem gamma_closed_ne_singleton (a b : VFType (M := M))
    (α : Values.Gamma (M := M)) : gammaBall a α false ≠ {b.val} := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  intro he
  have hsub : {x : VFType (M := M) | v (x-a) ≤ v r} ⊆ {x | v (x-b) ≤ v (0 : VFType (M := M))} := by
    intro x hx
    have hx' := (BallKindPredicates.gammaBall_mem_valuation_closed v hv a r α hr x).mpr hx
    rw [he] at hx'
    have hxb : x = b := Subtype.ext (show x.val = b.val from hx')
    simp only [hxb,sub_self,map_zero,le_refl]
  have hle := ValuationRadius.closed_radius_le_of_subset v a b r 0 hsub
  have hr0 : r = 0 := (map_eq_zero v).mp (le_zero_iff.mp (by simpa only [map_zero] using hle))
  have hz : Values.vfValueHom r = Values.infinity := by
    rw [hr0,map_zero]; exact Values.infinity_eq_zero.symm
  exact α.property (hr.symm.trans hz)

theorem gamma_radius_unique (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a b : VFType (M := M)) (α β : Values.Gamma (M := M)) (strict other : Bool)
    (he : gammaBall a α strict = gammaBall b β other) : α = β := by
  cases strict <;> cases other
  · exact gamma_radius_unique_same_kind a b α β false he
  · exact (gamma_open_ne_closed δ hδ b a β α he.symm).elim
  · exact (gamma_open_ne_closed δ hδ a b α β he).elim
  · exact gamma_radius_unique_same_kind a b α β true he

end IntegrationInACVF.Section3ACVF.BallRadiusGeometry
