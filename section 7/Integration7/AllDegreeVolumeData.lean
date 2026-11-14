import Integration7.VolumeDataRelabelingMaps
import Integration7.VolumeProductPointwise

/-! Uniform density-bearing product presentations. The toObject map
retains ordinary RV[0], while pointwise density identities remain available
before the degree-zero density is forgotten. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def rvVolumeDataOfObject (n : ℕ) (U : RVVolumeObject (M := M) S n) : RVVolumeData (M := M) S n :=
  ⟨rvVolumeUnderlying S n U,rvVolumeForm S n U⟩

@[simp] theorem rvVolumeDataOfObject_toObject (n : ℕ) (U : RVVolumeObject (M := M) S n) :
    (rvVolumeDataOfObject n U).toObject = U := by cases n <;> rfl

def rvVolumeProductData (n m : ℕ) (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    RVVolumeData (M := M) S (n+m) where
  underlying := rvFiniteProductObject (rvVolumeUnderlying S n U) (rvVolumeUnderlying S m V)
  form := ((rvVolumeForm S n U).prod (rvVolumeForm S m V)).pullback
    (rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain)

theorem RVVolumeData.toObject_eq_ofForm {n : ℕ} (D : RVVolumeData (M := M) S n) :
    D.toObject = rvVolumeOfForm S n D.underlying D.form := by cases n <;> rfl

@[simp] theorem rvVolumeProductData_toObject (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    (rvVolumeProductData n m U V).toObject = rvVolumeProduct S n m U V :=
  RVVolumeData.toObject_eq_ofForm (rvVolumeProductData n m U V)

theorem rvVolumeProductData_density_pair (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (u : (rvVolumeUnderlying S n U).obj.domain) (v : (rvVolumeUnderlying S m V).obj.domain) :
    (rvVolumeProductData n m U V).form.value
      (rvPackPair (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain u v) =
      (rvVolumeForm S n U).value u * (rvVolumeForm S m V).value v := by
  change ((rvVolumeForm S n U).prod (rvVolumeForm S m V)).value
    (rvUnpack _ _ (rvPackPair _ _ u v)) = _
  rw [rvUnpack_pair]
  rfl

theorem rvVolumeProduct_density_pair (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (u : (rvVolumeUnderlying S n U).obj.domain) (v : (rvVolumeUnderlying S m V).obj.domain) :
    (rvVolumeForm S (n+m) (rvVolumeProduct S n m U V)).value
      ((rvVolumeProduct_underlying n m U V).symm ▸ rvPackPair _ _ u v) =
      (rvVolumeForm S n U).value u * (rvVolumeForm S m V).value v := by
  have h := rvVolumeProduct_density n m U V (rvPackPair _ _ u v)
  simpa only [rvUnpack_pair] using h

end IntegrationInACVF.Section7
