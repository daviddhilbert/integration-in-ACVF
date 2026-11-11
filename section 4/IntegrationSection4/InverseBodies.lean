import IntegrationSection4.TranslationOffsets
import IntegrationSection3ACVF.GammaCosetGeometry
import Section5.RootConstruction

/-! Actual VF images of unary inverse RV-polydiscs, with the zero fibre
separated from ordinary open balls. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseBodies

open GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {m l : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}

def body (T : SpecialBijection A B) (b : B) : Set M :=
  {x | ∃ a : A, (vfAt a.val 0).val = x ∧ SameRV (T.toMap a).val b.val}

theorem body_nonempty (T : SpecialBijection A B) (b : B) : (body T b).Nonempty :=
  ⟨(vfAt (T.inverseMap b).val 0).val,T.inverseMap b,rfl,by rw [T.apply_inverse]; rfl⟩

theorem body_sameRV (T : SpecialBijection A B) (b c : B) (h : SameRV b.val c.val) :
    body T b = body T c := by
  ext x
  exact ⟨fun ⟨a,ha,he⟩ => ⟨a,ha,he.trans h⟩,
    fun ⟨a,ha,he⟩ => ⟨a,ha,he.trans h.symm⟩⟩

theorem body_zero (T : SpecialBijection A B) (b : B) (hb : vfAt b.val 0 = 0) :
    body T b = {(vfAt (T.inverseMap b).val 0).val} := by
  ext x
  constructor
  · rintro ⟨a,ha,he⟩
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
    have hZero : vfAt (T.toMap a).val 0 = 0 :=
      (rv_eq_zero_iff _).mp ((hv 0).trans (congrArg rv hb))
    have ht : T.toMap a = b := by
      apply Subtype.ext
      refine Prod.ext ?_ hl
      funext i
      fin_cases i
      exact hZero.trans hb.symm
    have hi : a = T.inverseMap b := by
      rw [← ht,T.inverse_apply]
    exact ha.symm.trans (congrArg (fun a : A => (vfAt a.val 0).val) hi)
  · intro hx
    refine ⟨T.inverseMap b,hx.symm,?_⟩
    rw [T.apply_inverse]
    rfl

theorem body_ordinary (T : SpecialBijection A B) (hB : IsRVPullback (carrier B))
    (b : B) (hb : vfAt b.val 0 ≠ 0) :
    ∃ γ : Values.Gamma (M := M), Values.vfValueHom (vfAt b.val 0) = γ.val ∧
      body T b = gammaBall (vfAt (T.inverseMap b).val 0) γ true := by
  have hFinite : Values.vfValueHom (vfAt b.val 0) ≠ Values.infinity := by
    intro he
    exact hb ((CanonicalRV.encodedRv_zero_iff _).mp
      ((Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (vfAt b.val 0))).mp he))
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (vfAt b.val 0),hFinite⟩
  let v := Values.presentationValuation (M := M)
  have hv := Values.presentation_compatible (M := M)
  have hF := (T.unary_inverse_fibre v hv hB b hb).1
  refine ⟨γ,rfl,?_⟩
  ext x
  constructor
  · rintro ⟨a,ha,he⟩
    have hp : a.val ∈ T.inverseFibre b := ⟨a,rfl,he⟩
    rw [hF] at hp
    rw [← ha]
    exact (GammaCosetGeometry.gammaBall_mem_valuation v hv
      (vfAt (T.inverseMap b).val 0) (vfAt b.val 0) γ rfl (vfAt a.val 0)).mpr hp.1
  · intro hx
    let X : VF (M := M) := ⟨x,hx.1⟩
    let p : Point (M := M) 1 m := unaryPoint X (T.inverseMap b).val.2
    have hp : p ∈ T.inverseFibre b := by
      rw [hF]
      exact ⟨(GammaCosetGeometry.gammaBall_mem_valuation v hv
        (vfAt (T.inverseMap b).val 0) (vfAt b.val 0) γ rfl X).mp hx,rfl⟩
    obtain ⟨a,ha,he⟩ := hp
    exact ⟨a,congrArg (fun p : Point (M := M) 1 m => (vfAt p 0).val) ha,he⟩

theorem body_contains_source (T : SpecialBijection A B) (a : A) :
    (vfAt a.val 0).val ∈ body T (T.toMap a) := ⟨a,rfl,rfl⟩

end IntegrationInACVF.Section4.InverseBodies
