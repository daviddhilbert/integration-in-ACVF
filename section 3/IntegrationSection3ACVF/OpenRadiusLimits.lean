import IntegrationSection3ACVF.AnnulusValueIntervals
import IntegrationSection3ACVF.LinearRadiusThreshold

/-! Ordinary open balls are unions of their strictly smaller concentric
open balls, in the actual Gamma order, including pairs through the centre. -/

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

namespace IntegrationInACVF.Section3ACVF.OpenRadiusLimits

open GammaRadiusAtomicity AnnulusValueIntervals

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nested (c : VFType (M := M)) (α β : Values.Gamma (M := M)) (hαβ : α ≤ β) :
    gammaBall c β true ⊆ gammaBall c α true := by
  intro z hz
  let x : VFType (M := M) := ⟨z,hz.1⟩
  have hαβ' : α.val ≤ β.val := hαβ
  exact (mem_open c x α).mpr (hαβ'.trans_lt ((mem_open c x β).mp hz))

theorem exists_smaller_radius (c x : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hx : x.val ∈ gammaBall c ρ true) :
    ∃ γ : Values.Gamma (M := M), ρ < γ ∧ x.val ∈ gammaBall c γ true := by
  by_cases he : x = c
  · obtain ⟨γ,hργ⟩ := exists_gt ρ
    subst x
    exact ⟨γ,hργ,BallEnlargementGeometry.gammaBall_centre_mem c γ true⟩
  · have hFinite : Values.vfValueHom (x-c) ≠ Values.infinity := by
      intro h
      have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (x-c))).mp h
      exact (sub_ne_zero.mpr he) ((CanonicalRV.encodedRv_zero_iff (x-c)).mp hz)
    let η : Values.Gamma (M := M) := ⟨Values.vfValueHom (x-c),hFinite⟩
    have hρη : ρ < η := (mem_open c x ρ).mp hx
    obtain ⟨γ,hργ,hγη⟩ := exists_between hρη
    exact ⟨γ,hργ,(mem_open c x γ).mpr hγη⟩

theorem pair_smaller_radius (c x y : VFType (M := M)) (ρ : Values.Gamma (M := M))
    (hx : x.val ∈ gammaBall c ρ true) (hy : y.val ∈ gammaBall c ρ true) :
    ∃ γ : Values.Gamma (M := M), ρ < γ ∧ x.val ∈ gammaBall c γ true ∧ y.val ∈ gammaBall c γ true := by
  obtain ⟨α,hρα,hxα⟩ := exists_smaller_radius c x ρ hx
  obtain ⟨β,hρβ,hyβ⟩ := exists_smaller_radius c y ρ hy
  exact ⟨min α β,lt_min hρα hρβ,nested c _ α (min_le_left _ _) hxα,nested c _ β (min_le_right _ _) hyβ⟩

theorem distinct_points (c : VFType (M := M)) (ρ : Values.Gamma (M := M)) :
    ∃ x y : VFType (M := M), x.val ∈ gammaBall c ρ true ∧ y.val ∈ gammaBall c ρ true ∧ x ≠ y := by
  obtain ⟨γ,hργ⟩ := exists_gt ρ
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  have hr0 : r ≠ 0 := by
    intro he
    have hi : Values.vfValueHom r = Values.infinity := by
      rw [he,map_zero]
      exact Values.infinity_eq_zero.symm
    exact γ.property (hr.symm.trans hi)
  refine ⟨c,c+r,BallEnlargementGeometry.gammaBall_centre_mem c ρ true,?_,?_⟩
  · apply (mem_open c (c+r) ρ).mpr
    have he : c+r-c = r := by abel
    rw [he,hr]
    exact hργ
  · intro he
    have h : r = 0 := by
      have hc := congrArg (fun z => z-c) he.symm
      have hCancel : c+r-c = r := by abel
      rwa [hCancel,sub_self] at hc
    exact hr0 h

end IntegrationInACVF.Section3ACVF.OpenRadiusLimits
