import IntegrationSection3ACVF.FullGammaRadius
import IntegrationSection3.InfiniteCosets

/-! Genuine ball geometry for the infinite-class input to Lemma 3.9. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open IntegrationInACVF.Section3
open SpecialTransformations.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.GammaCosetGeometry

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem vf_representative (γ : Values.Gamma (M := M)) :
    ∃ r : VFType (M := M), Values.vfValueHom r = γ.val := by
  obtain ⟨t,_,ht⟩ := Values.gamma_has_nonzero_representative γ
  obtain ⟨r,hr⟩ := CanonicalRV.encodedRv_surjective t
  exact ⟨r,(congrArg Values.vrv hr).trans ht⟩

theorem gammaBall_mem_valuation {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (a r : VFType (M := M)) (γ : Values.Gamma (M := M))
    (hr : Values.vfValueHom r = γ.val) (x : VFType (M := M)) :
    x.val ∈ gammaBall a γ true ↔ v (x-a) < v r := by
  rw [← radiusBall_eq_gammaBall a (CanonicalRV.encodedRv r) γ hr true]
  change (iVF x.val ∧ iLe (iRv r.val) (iRv (iVFAdd x.val (iVFNeg a.val))) ∧
    (true = true → ¬ iLe (iRv (iVFAdd x.val (iVFNeg a.val))) (iRv r.val))) ↔ _
  simp only [and_iff_right x.property,true_implies]
  have hd : (x-a).val = iVFAdd x.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
  rw [← hd]
  change (VFValued.predV (x-a) r ∧ ¬ VFValued.predV r (x-a)) ↔ _
  rw [hv,hv,lt_iff_le_not_ge]

theorem valuation_nat_unit {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (h00 : M ⊨ Axioms.ACVF00) (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (n : ℕ) (hn : n ≠ 0) : v (n : VFType (M := M)) = 1 := by
  have h1 : Average.val (1 : VFType (M := M)) = iRVOne := Average.val_one
  have hl : VFValued.predV (n : VFType (M := M)) (1 : VFType (M := M)) := by
    have h : iLe (Average.val (1 : VFType (M := M))) (Average.val (n : VFType (M := M))) := by
      rw [h1]
      exact Average.le_one_natCast n
    exact h
  have hu : VFValued.predV (1 : VFType (M := M)) (n : VFType (M := M)) := by
    have h : iLe (Average.val (n : VFType (M := M))) (Average.val (1 : VFType (M := M))) := by
      rw [h1]
      exact Average.nat_unit h00 n hn
    exact h
  exact le_antisymm (by simpa only [map_one] using (hv _ _).mp hl)
    (by simpa only [map_one] using (hv _ _).mp hu)

theorem cosetBody_mem (H : AddSubgroup (VFType (M := M))) (x a : VFType (M := M)) :
    x.val ∈ cosetBody H a ↔ QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H a := by
  constructor
  · rintro ⟨u,hu,he⟩
    exact (Subtype.ext he : u=x) ▸ hu
  · intro h
    exact ⟨x,h,rfl⟩

/-- Every larger ordinary Gamma radius defines infinitely many open
subball cosets inside a given proper open ball. No centre is named in B. -/
theorem infinite_gamma_cosets (h00 : M ⊨ Axioms.ACVF00)
    (H : AddSubgroup (VFType (M := M)))
    (β : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a β true)
    (a : VFType (M := M)) (α : Values.Gamma (M := M)) (hαβ : α < β) :
    (QuotientAddGroup.mk' H '' {x : VFType (M := M) | x.val ∈ gammaBall a α true}).Infinite := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := vf_representative β
  obtain ⟨s,hs⟩ := vf_representative α
  have hm (x : VFType (M := M)) : x ∈ H ↔ v x < v r := by
    have h0 : x ∈ H ↔ x.val ∈ cosetBody H 0 := by
      rw [cosetBody_mem]
      constructor
      · intro hx
        apply QuotientAddGroup.eq_iff_sub_mem.mpr
        simpa only [sub_zero] using hx
      · intro he
        have hx : x - (0 : VFType (M := M)) ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp he
        simpa only [sub_zero] using hx
    rw [hH 0] at h0
    simpa only [sub_zero] using h0.trans (gammaBall_mem_valuation v hv 0 r β hr x)
  have hrs : v r < v s := by
    have hl : ¬ v s ≤ v r := by
      intro he
      have hp := (Values.vf_pred_iff_gamma_le s r).mp ((hv s r).mpr he)
      rw [hr,hs] at hp
      exact not_le_of_gt hαβ hp
    exact lt_of_not_ge hl
  have hi := InfiniteCosets.infinite_cosets_in_open_ball v (valuation_nat_unit h00 v hv) H r hm a (v s) hrs
  convert hi using 1
  ext q
  apply exists_congr
  intro x
  exact and_congr_left (fun _ => gammaBall_mem_valuation v hv a s α hs x)



theorem gammaBall_coded (a : VFType (M := M)) (α : Values.Gamma (M := M)) :
    ∃ i : BallImaginaries.Ball M, BallImaginaries.underlying i = gammaBall a α true := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := vf_representative α
  have hr0 : r ≠ 0 := by
    intro he
    have hz : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact α.property (hr.symm.trans hz)
  obtain ⟨i,hi⟩ := BallImaginaries.open_disc_coded v hv a r hr0
  have hf : {x : VFType (M := M) | x.val ∈ BallImaginaries.underlying i} =
      {x : VFType (M := M) | x.val ∈ gammaBall a α true} := by
    rw [hi]
    ext x
    exact (gammaBall_mem_valuation v hv a r α hr x).symm
  refine ⟨i,Set.ext fun x => ?_⟩
  constructor
  · intro hx
    exact (Set.ext_iff.mp hf (⟨x,BallImaginaries.underlying_subset_vf i hx⟩ : VFType (M := M))).mp hx
  · intro hx
    exact (Set.ext_iff.mp hf (⟨x,hx.choose⟩ : VFType (M := M))).mpr hx

theorem intermediate_radius (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (x y : VFType (M := M)) (hx : x.val ∈ gammaBall a α true)
    (hy : y.val ∈ gammaBall a α true) (hne : x ≠ y) :
    ∃ β : Values.Gamma (M := M), α < β ∧ β.val < Values.vfValueHom (x-y) := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨s,hs⟩ := vf_representative α
  have hxv := (gammaBall_mem_valuation v hv a s α hs x).mp hx
  have hyv := (gammaBall_mem_valuation v hv a s α hs y).mp hy
  have hd : v (x-y) < v s := by
    have h := v.map_sub_lt hxv hyv
    have he : (x-a)-(y-a) = x-y := by ring
    rwa [he] at h
  have hd0 : Values.vfValueHom (x-y) ≠ Values.infinity := by
    intro he
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (x-y))).mp he
    exact hne (sub_eq_zero.mp ((CanonicalRV.encodedRv_zero_iff (x-y)).mp hz))
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (x-y),hd0⟩
  have hαγ : α < γ := by
    apply lt_of_not_ge
    intro he
    have hp : VFValued.predV s (x-y) := (Values.vf_pred_iff_gamma_le s (x-y)).mpr (by
      rw [hs]
      exact he)
    exact not_le_of_gt hd ((hv s (x-y)).mp hp)
  obtain ⟨β,hαβ,hβγ⟩ := exists_between hαγ
  exact ⟨β,hαβ,hβγ⟩

theorem same_coset_of_difference (H : AddSubgroup (VFType (M := M)))
    (β : Values.Gamma (M := M))
    (hH : ∀ a : VFType (M := M), cosetBody H a = gammaBall a β true)
    (x y : VFType (M := M)) (hxy : β.val < Values.vfValueHom (x-y)) :
    QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H y := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := vf_representative β
  have hlt : v (x-y) < v r := by
    apply lt_of_not_ge
    intro he
    have hp := (Values.vf_pred_iff_gamma_le r (x-y)).mp ((hv r (x-y)).mpr he)
    rw [hr] at hp
    exact not_le_of_gt hxy hp
  apply (cosetBody_mem H x y).mp
  rw [hH y]
  exact (gammaBall_mem_valuation v hv y r β hr x).mpr hlt

end IntegrationInACVF.Section3ACVF.GammaCosetGeometry
