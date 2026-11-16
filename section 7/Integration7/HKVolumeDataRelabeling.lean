module

public import Integration7.HKRVVolumeProducts
public import Integration7.VolumeDataRelabelingMaps

@[expose] public section

/-! Density-bearing relabeling in every degree, including exact degree zero. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def dataOfObject (n : ℕ) (U : RVVolumeObject (M := M) S n) : RVVolumeData (M := M) S n :=
  ⟨underlying S n U, form S n U⟩

@[simp] theorem dataOfObject_ofData (n : ℕ) (U : RVVolumeObject (M := M) S n) :
    ofData (dataOfObject n U) = U := by cases n <;> rfl

def dataRelabelIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (D E : RVVolumeData (M := M) (C.base : Set M) n)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u) :
    rvVolumeIsoInDegree (C.base : Set M) n (ofData D) (ofData E) := by
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
    (U := D.underlying.obj) (V := E.underlying.obj) F hF hcoord)
  cases n with
  | zero => exact ⟨e, fun u => (hφ u).symm⟩
  | succ n =>
    exact RVVolumeIso.of_preserving_coordinates_full hc C e hcoord hφ

def dataReindexedIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} (h : n=m) (D : RVVolumeData (M := M) (C.base : Set M) n)
    (E : RVVolumeData (M := M) (C.base : Set M) m)
    (F : Map D.underlying.obj.domain E.underlying.obj.domain) (hF : Function.Bijective F)
    (hcoord : ∀ u, E.underlying.obj.value (F u) ∘ finCongr h = D.underlying.obj.value u)
    (hφ : ∀ u, E.form.value (F u) = D.form.value u) :
    rvVolumeIsoInDegree (C.base : Set M) n (ofData D) (h.symm ▸ ofData E) := by
  cases h
  exact dataRelabelIso hc C D E F hF hcoord hφ

def productData (n m : ℕ) (U : RVVolumeObject (M := M) S n)
    (V : RVVolumeObject (M := M) S m) : RVVolumeData (M := M) S (n+m) where
  underlying := rvFiniteProductObject (underlying S n U) (underlying S m V)
  form := ((form S n U).prod (form S m V)).pullback
    (rvUnpack (underlying S n U).obj.domain (underlying S m V).obj.domain)

@[simp] theorem productData_ofData (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    ofData (productData n m U V) = product S n m U V := rfl

theorem productData_density_pair (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (u : (underlying S n U).obj.domain) (v : (underlying S m V).obj.domain) :
    (productData n m U V).form.value (rvPackPair _ _ u v) =
      (form S n U).value u * (form S m V).value v := by
  change ((form S n U).prod (form S m V)).value (rvUnpack _ _ (rvPackPair _ _ u v)) = _
  rw [rvUnpack_pair]
  rfl

theorem product_density_pair (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (u : (underlying S n U).obj.domain) (v : (underlying S m V).obj.domain) :
    (form S (n+m) (product S n m U V)).value
      ((product_underlying n m U V).symm ▸ rvPackPair _ _ u v) =
      (form S n U).value u * (form S m V).value v := by
  have h := product_density n m U V (rvPackPair _ _ u v)
  rw [rvUnpack_pair] at h
  exact h

end IntegrationInACVF.Section7.HK
