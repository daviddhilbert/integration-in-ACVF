module

public import Integration7.HKVolumeCoproducts
public import Integration7.HKRVProductIsomorphisms
public import Section4.EmptyMaps

@[expose] public section

/-! The actual empty object absorbs the original product in every
degree. All volume equations hold on its genuinely empty domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

theorem empty_domain (n : ℕ) :
    (underlying S n (empty (M := M) S n)).obj.domain.carrier = ∅ := by cases n <;> rfl

def productRightZeroIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (product _ n m U (empty _ m)) (empty _ (n+m)) := by
  let D := productData n m U (empty (C.base : Set M) m)
  let E := dataOfObject (n+m) (empty (C.base : Set M) (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack (underlying (C.base : Set M) n U).obj.domain
      (underlying (C.base : Set M) m (empty (C.base : Set M) m)).obj.domain ⟨x,hx⟩
    exact (empty_domain (S := (C.base : Set M)) m).le p.property.2
  have hE : E.underlying.obj.domain.carrier = ∅ := empty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := dataRelabelIso hc C D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
  simpa only [D,E,productData_ofData,dataOfObject_ofData] using h

def productLeftZeroIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) {n m : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) m) :
    rvVolumeIsoInDegree (C.base : Set M) (n+m)
      (product _ n m (empty _ n) U) (empty _ (n+m)) := by
  let D := productData n m (empty (C.base : Set M) n) U
  let E := dataOfObject (n+m) (empty (C.base : Set M) (n+m))
  have hD : D.underlying.obj.domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let p := rvUnpack
      (underlying (C.base : Set M) n (empty (C.base : Set M) n)).obj.domain
      (underlying (C.base : Set M) m U).obj.domain ⟨x,hx⟩
    exact (empty_domain (S := (C.base : Set M)) n).le p.property.1
  have hE : E.underlying.obj.domain.carrier = ∅ := empty_domain (n+m)
  let F := Map.fromEmpty hD E.underlying.obj.domain
  have h := dataRelabelIso hc C D E F (Map.bijective_of_empty F hD hE)
    (fun x => (hD.le x.property).elim) (fun x => (hD.le x.property).elim)
  simpa only [D,E,productData_ofData,dataOfObject_ofData] using h

end IntegrationInACVF.Section7.HK
