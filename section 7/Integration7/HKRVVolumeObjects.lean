module

public import Integration7.UniformVolumeData
public import Integration7.GradedVolumeProducts

@[expose] public section

/-! The corrected all-degree presentation retains the actual form at zero.
Positive objects are the existing checked objects. The HK namespace stages
the correction without changing the types of the legacy all-degree API. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

structure ZeroRVVolumeObject (S : Set M) where
  underlying : RVFiniteObject (M := M) S 0
  form : VolumeForm underlying.obj.domain

abbrev RVVolumeObject (S : Set M) : ℕ → Type
  | 0 => ZeroRVVolumeObject (M := M) S
  | k+1 => PositiveRVVolumeObject (M := M) S k

def underlying (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n → RVFiniteObject (M := M) S n
  | 0, U => U.underlying
  | _+1, U => U.underlying

def form (S : Set M) : (n : ℕ) → (U : RVVolumeObject (M := M) S n) →
    VolumeForm (underlying S n U).obj.domain
  | 0, U => U.form
  | _+1, U => U.form

def ofForm (S : Set M) : (n : ℕ) → (U : RVFiniteObject (M := M) S n) →
    VolumeForm U.obj.domain → RVVolumeObject (M := M) S n
  | 0, U, ω => ⟨U, ω⟩
  | _+1, U, ω => ⟨U, ω⟩

@[simp] theorem ofForm_underlying (n : ℕ) (U : RVFiniteObject (M := M) S n)
    (ω : VolumeForm U.obj.domain) : underlying S n (ofForm S n U ω) = U := by
  cases n <;> rfl

theorem ofForm_density (n : ℕ) (U : RVFiniteObject (M := M) S n)
    (ω : VolumeForm U.obj.domain) (a : U.obj.domain) :
    (form S n (ofForm S n U ω)).value ((ofForm_underlying n U ω).symm ▸ a) = ω.value a := by
  cases n <;> rfl

def ofData {n : ℕ} (D : RVVolumeData (M := M) S n) : RVVolumeObject (M := M) S n :=
  ofForm S n D.underlying D.form

@[simp] theorem ofData_underlying {n : ℕ} (D : RVVolumeData (M := M) S n) :
    underlying S n (ofData D) = D.underlying := ofForm_underlying _ _ _

def ZeroRVVolumeObject.unitForm (Z : RVFiniteObject (M := M) S 0) : ZeroRVVolumeObject (M := M) S :=
  ⟨Z, VolumeForm.one Z.obj.domain⟩

@[simp] theorem ZeroRVVolumeObject.unitForm_density (Z : RVFiniteObject (M := M) S 0)
    (z : Z.obj.domain) : (ZeroRVVolumeObject.unitForm Z).form.value z = 1 := rfl

end IntegrationInACVF.Section7.HK
