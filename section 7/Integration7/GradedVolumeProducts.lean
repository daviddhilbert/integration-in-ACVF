import Integration7.VolumeFormProducts
import Integration7.RVVolumeObjects
import Section4.RVFiniteHomogeneousProducts
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def VolumeForm.one {P : Space LRV M} (A : DefSet P S) : VolumeForm A where
  map := rvScalarOne A
  nonzero _ := one_ne_zero

@[simp] theorem VolumeForm.one_value {P : Space LRV M} (A : DefSet P S) (a : A) :
    (VolumeForm.one A).value a = 1 := rfl

def rvVolumeUnderlying (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n → RVFiniteObject (M := M) S n
  | 0, U => U
  | _+1, U => U.underlying

def rvVolumeForm (S : Set M) : (n : ℕ) → (U : RVVolumeObject (M := M) S n) →
    VolumeForm (rvVolumeUnderlying S n U).obj.domain
  | 0, U => VolumeForm.one U.obj.domain
  | _+1, U => U.form

def rvVolumeOfForm (S : Set M) : (n : ℕ) → (U : RVFiniteObject (M := M) S n) →
    VolumeForm U.obj.domain → RVVolumeObject (M := M) S n
  | 0, U, _ => U
  | _+1, U, ω => ⟨U, ω⟩

@[simp] theorem rvVolumeOfForm_underlying (n : ℕ) (U : RVFiniteObject (M := M) S n)
    (ω : VolumeForm U.obj.domain) :
    rvVolumeUnderlying S n (rvVolumeOfForm S n U ω) = U := by
  cases n <;> rfl

theorem rvVolumeOfForm_density (n : ℕ) (U : RVFiniteObject (M := M) S n)
    (ω : VolumeForm U.obj.domain) (hω : n = 0 → ∀ a, ω.value a = 1) (a : U.obj.domain) :
    (rvVolumeForm S n (rvVolumeOfForm S n U ω)).value
      ((rvVolumeOfForm_underlying n U ω).symm ▸ a) = ω.value a := by
  cases n with
  | zero => exact (hω rfl a).symm
  | succ n => rfl

def PositiveRVVolumeObject.prod {n m : ℕ}
    (U : PositiveRVVolumeObject (M := M) S n) (V : PositiveRVVolumeObject (M := M) S m) :
    PositiveRVVolumeObject (M := M) S ((n+1)+m) where
  underlying := rvFiniteProductObject (k := n+1) (l := m+1) U.underlying V.underlying
  form := (U.form.prod V.form).pullback (rvUnpack U.underlying.obj.domain V.underlying.obj.domain)

def rvVolumeProduct (S : Set M) (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    RVVolumeObject (M := M) S (n+m) :=
  rvVolumeOfForm S (n+m)
    (rvFiniteProductObject (k := n) (l := m) (rvVolumeUnderlying S n U) (rvVolumeUnderlying S m V))
    (((rvVolumeForm S n U).prod (rvVolumeForm S m V)).pullback
      (rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain))

@[simp] theorem rvVolumeProduct_underlying (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m) :
    rvVolumeUnderlying S (n+m) (rvVolumeProduct S n m U V) =
      rvFiniteProductObject (k := n) (l := m) (rvVolumeUnderlying S n U) (rvVolumeUnderlying S m V) :=
  rvVolumeOfForm_underlying _ _ _

theorem rvVolumeProduct_density (n m : ℕ)
    (U : RVVolumeObject (M := M) S n) (V : RVVolumeObject (M := M) S m)
    (a : (rvFiniteProductObject (rvVolumeUnderlying S n U) (rvVolumeUnderlying S m V)).obj.domain) :
    (rvVolumeForm S (n+m) (rvVolumeProduct S n m U V)).value
      ((rvVolumeProduct_underlying n m U V).symm ▸ a) =
      (rvVolumeForm S n U).value
        ⟨(rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain a).val.1,
          (rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain a).property.1⟩ *
      (rvVolumeForm S m V).value
        ⟨(rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain a).val.2,
          (rvUnpack (rvVolumeUnderlying S n U).obj.domain (rvVolumeUnderlying S m V).obj.domain a).property.2⟩ := by
  apply rvVolumeOfForm_density
  intro h a
  obtain ⟨rfl, rfl⟩ := Nat.add_eq_zero_iff.mp h
  exact one_mul 1
end IntegrationInACVF.Section7
