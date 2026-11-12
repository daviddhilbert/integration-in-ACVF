import IntegrationSection6.GammaFamilyRows
import IntegrationSection6.GammaNativeFiniteBounds

/-! Raw parameter rows are exactly the typed family rows, including all
proper-sort restrictions. Their actual graph presentations retain the
same raw domain and volume sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ}

theorem GammaRVFamilyFormula.raw_row_domain_iff (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M)) (x : Fin a → M) :
    Fin.append (fun j => (z j).val) x ∈ (F.schema N).domain ↔
      ∃ t : Fin a → RV (M := M), t ∈ F.rowDomain z ∧ (fun j => (t j).val) = x := by
  constructor
  · rintro ⟨q,hq,he⟩
    have hv : q.1 = z := by
      funext j
      apply Subtype.ext
      simpa only [gammaPointCode,vfAt,Fin.append_left] using congrFun he (Fin.castAdd a j)
    refine ⟨q.2,?_,funext (fun j => ?_)⟩
    · change (z,q.2) ∈ F.domain
      rw [← hv]
      exact hq
    · simpa only [gammaPointCode,Fin.append_right] using congrFun he (Fin.natAdd p j)
  · rintro ⟨t,ht,he⟩
    refine ⟨(z,t),ht,?_⟩
    exact congrArg (Fin.append (fun j => (z j).val)) he

theorem GammaRVFamilyFormula.raw_row_volume_iff (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M)) (x : Fin a → M) (y : Fin k → M) :
    Fin.append (Fin.append (fun j => (z j).val) x) y ∈ (F.schema N).volume ↔
      ∃ t : Fin a → RV (M := M), ∃ s : Fin k → RV (M := M),
        F.rowVolume z t s ∧ (fun j => (t j).val) = x ∧ (fun j => (s j).val) = y := by
  constructor
  · rintro ⟨q,r,hqr,he⟩
    have hq : gammaPointCode q = Fin.append (fun j => (z j).val) x := by
      funext j
      simpa only [Fin.append_left] using congrFun he (Fin.castAdd k j)
    have hv : q.1 = z := by
      funext j
      apply Subtype.ext
      simpa only [gammaPointCode,vfAt,Fin.append_left] using congrFun hq (Fin.castAdd a j)
    have hr : r = (Fin.elim0,r.2) := Prod.ext (Subsingleton.elim _ _) rfl
    refine ⟨q.2,r.2,?_,funext (fun j => ?_),funext (fun j => ?_)⟩
    · change F.volume (z,q.2) (Fin.elim0,r.2)
      rw [← hv,← hr]
      exact hqr
    · simpa only [gammaPointCode,Fin.append_right] using congrFun hq (Fin.natAdd p j)
    · simpa only [Fin.append_right] using congrFun he (Fin.natAdd (p+a) j)
  · rintro ⟨t,s,hv,hx,hy⟩
    refine ⟨(z,t),(Fin.elim0,s),hv,?_⟩
    exact congrArg₂ Fin.append (congrArg (Fin.append (fun j => (z j).val)) hx) hy

theorem GammaRVFamilyFormula.raw_row_domain_presented (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (x : Fin a → M) :
    Fin.append (fun j => (z j).val) x ∈ (F.schema N).domain ↔ x ∈ gammaRawObjectDomain P.toGamma.toGammaRVObject := by
  rw [F.raw_row_domain_iff]
  constructor
  · rintro ⟨t,ht,hx⟩
    exact ⟨⟨t,(Set.ext_iff.mp P.domain_eq t).mpr ht⟩,hx⟩
  · rintro ⟨u,hu⟩
    exact ⟨u.val,((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).1,hu⟩

theorem GammaRVFamilyFormula.raw_row_volume_presented (F : GammaRVFamilyFormula B p a k) (N : ℕ)
    (z : Fin p → VF (M := M))
    (hsupport : ∀ t s, F.rowVolume z t s → t ∈ F.rowDomain z)
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (z j).val),B.gamma⟩ a k
      (F.rowDomain z) (F.rowVolume z)) (x : Fin a → M) (y : Fin k → M) :
    Fin.append (Fin.append (fun j => (z j).val) x) y ∈ (F.schema N).volume ↔
      Fin.append x y ∈ gammaRawObjectVolume P.toGamma.toGammaRVObject := by
  rw [F.raw_row_volume_iff,gammaRawObjectVolume_append_iff]
  constructor
  · rintro ⟨t,s,hv,hx,hy⟩
    obtain ⟨u,hu,hs⟩ := (P.graph_iff t s).mpr ⟨hsupport t s hv,hv⟩
    refine ⟨u,?_,?_⟩
    · exact (congrArg (fun v => fun j => (v j).val) hu).trans hx
    · exact (congrArg (fun v => fun j => (v j).val) hs).trans hy
  · rintro ⟨u,hu,hv⟩
    exact ⟨u.val,gammaVolumeValue P.toGamma.toGammaRVObject u,
      ((P.graph_iff u.val (P.volume u).val).mp ⟨u,rfl,rfl⟩).2,hu,hv⟩

end IntegrationInACVF.Section6
