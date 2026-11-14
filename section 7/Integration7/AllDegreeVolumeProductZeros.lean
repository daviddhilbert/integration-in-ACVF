import Integration7.AllDegreeVolumeCoproductData
import Section4.EmptyMaps

/-! The actual empty object absorbs the original product in every
degree. All volume equations hold on its genuinely empty domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem rvVolumeEmpty_domain (n : ℕ) :
    (rvVolumeUnderlying S n (rvVolumeEmpty (M := M) S n)).obj.domain.carrier = ∅ := by cases n <;> rfl

def rvVolumeProductRightZeroIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeProduct _ n m U (rvVolumeEmpty _ m)) (rvVolumeEmpty _ (n+m)) := by
  let D := rvVolumeProductData n m U (rvVolumeEmpty (C.base : Set M) m)
  let E := rvVolumeDataOfObject (n+m) (rvVolumeEmpty (C.base : Set M) (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack (rvVolumeUnderlying (C.base : Set M) n U).obj.domain
      (rvVolumeUnderlying (C.base : Set M) m (rvVolumeEmpty (C.base : Set M) m)).obj.domain ⟨x,hx⟩
    exact (rvVolumeEmpty_domain (S := (C.base : Set M)) m).le p.property.2
  have hE : E.underlying.obj.domain.carrier = ∅ := rvVolumeEmpty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := rvVolumeDataRelabelIso hc C D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
  simpa only [D,E,rvVolumeProductData_toObject,rvVolumeDataOfObject_toObject] using h

def rvVolumeProductLeftZeroIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) m) :
    RVVolumeIsoInDegree (C.base : Set M) (n+m)
      (rvVolumeProduct _ n m (rvVolumeEmpty _ n) U) (rvVolumeEmpty _ (n+m)) := by
  let D := rvVolumeProductData n m (rvVolumeEmpty (C.base : Set M) n) U
  let E := rvVolumeDataOfObject (n+m) (rvVolumeEmpty (C.base : Set M) (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack
      (rvVolumeUnderlying (C.base : Set M) n (rvVolumeEmpty (C.base : Set M) n)).obj.domain
      (rvVolumeUnderlying (C.base : Set M) m U).obj.domain ⟨x,hx⟩
    exact (rvVolumeEmpty_domain (S := (C.base : Set M)) n).le p.property.1
  have hE : E.underlying.obj.domain.carrier = ∅ := rvVolumeEmpty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := rvVolumeDataRelabelIso hc C D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
  simpa only [D,E,rvVolumeProductData_toObject,rvVolumeDataOfObject_toObject] using h

end IntegrationInACVF.Section7
