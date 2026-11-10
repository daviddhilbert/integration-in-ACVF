import IntegrationSection3ACVF.BallEnlargementGeometry

/-! Infinitude of ordinary balls, using actual valuation density
and the residue-characteristic-zero integer-translate construction. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.InfiniteOrdinaryBalls

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem open_infinite (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    (gammaBall a α true).Infinite := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative α
  have hr0 : r ≠ 0 := by
    intro he
    have hInf : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact α.property (hr.symm.trans hInf)
  have hpos : 0 < v r := zero_lt_iff.mpr ((v.ne_zero_iff).mpr hr0)
  obtain ⟨u,hu0,hur⟩ := BallRadiusGeometry.valuation_dense v hv δ hδ 0 r (by
    simpa only [map_zero] using hpos)
  have hu0' : v u ≠ 0 := ne_of_gt (by simpa only [map_zero] using hu0)
  let H := v.ltAddSubgroup (Units.mk0 (v u) hu0')
  have hH (x : VFType (M := M)) : x ∈ H ↔ v x < v u := Iff.rfl
  have hqInf := InfiniteCosets.infinite_cosets_in_open_ball v
    (GammaCosetGeometry.valuation_nat_unit h00 v hv) H u hH a (v r) hur
  have hNative : ({x : VFType (M := M) | v (x-a) < v r} : Set (VFType (M := M))).Infinite :=
    fun hfin => hqInf (hfin.image (QuotientAddGroup.mk' H))
  intro hfin
  have hpull : ({x : VFType (M := M) | x.val ∈ gammaBall a α true} :
      Set (VFType (M := M))).Finite := hfin.preimage Subtype.val_injective.injOn
  apply hNative
  convert hpull using 1
  ext x
  exact (GammaCosetGeometry.gammaBall_mem_valuation v hv a r α hr x).symm

theorem closed_infinite (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    (gammaBall a α false).Infinite :=
  (open_infinite h00 δ hδ a α).mono
    (BallEnlargementGeometry.open_inside_closed_same_radius a a α
      (BallEnlargementGeometry.gammaBall_centre_mem a α false)).1

end IntegrationInACVF.Section3ACVF.InfiniteOrdinaryBalls
