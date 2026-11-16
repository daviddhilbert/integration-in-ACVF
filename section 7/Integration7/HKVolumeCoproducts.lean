import Integration7.HKVolumeDataRelabeling
import Integration7.AllDegreeVolumeCoproductData

/-! Coproducts glue the actual form on each summand in every degree. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}

def coprod (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n →
    RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n
  | 0,U,V => ofData ((dataOfObject 0 U).coprod (dataOfObject 0 V))
  | _+1,U,V => U.coprod V

def empty (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n
  | 0 => ZeroRVVolumeObject.unitForm (rvFiniteEmpty S 0)
  | k+1 => PositiveRVVolumeObject.empty S k

def unit (S : Set M) : ZeroRVVolumeObject (M := M) S :=
  ZeroRVVolumeObject.unitForm (rvFiniteUnitObject S)

@[simp] theorem data_coprod_ofData {n : ℕ} (D E : RVVolumeData (M := M) S n) :
    ofData (D.coprod E) = coprod S n (ofData D) (ofData E) := by cases n <;> rfl

@[simp] theorem coprod_underlying (n : ℕ) (U V : RVVolumeObject (M := M) S n) :
    underlying S n (coprod S n U V) = rvFiniteCoprodObject (underlying S n U) (underlying S n V) := by
  cases n <;> rfl

theorem coprod_density_left (n : ℕ) (U V : RVVolumeObject (M := M) S n)
    (u : (underlying S n U).obj.domain) :
    (form S n (coprod S n U V)).value ((coprod_underlying n U V).symm ▸
      rvCoprodLeftMap (underlying S n U).obj (underlying S n V).obj u) = (form S n U).value u := by
  cases n with
  | zero => exact RVVolumeData.coprod_density_left (dataOfObject 0 U) (dataOfObject 0 V) u
  | succ k => exact IntegrationInACVF.Section7.coprod_density_left U V u

theorem coprod_density_right (n : ℕ) (U V : RVVolumeObject (M := M) S n)
    (v : (underlying S n V).obj.domain) :
    (form S n (coprod S n U V)).value ((coprod_underlying n U V).symm ▸
      rvCoprodRightMap (underlying S n U).obj (underlying S n V).obj v) = (form S n V).value v := by
  cases n with
  | zero => exact RVVolumeData.coprod_density_right (dataOfObject 0 U) (dataOfObject 0 V) v
  | succ k => exact IntegrationInACVF.Section7.coprod_density_right U V v

theorem zero_coprod_cases (U V : ZeroRVVolumeObject (M := M) S)
    (w : (coprod S 0 U V).underlying.obj.domain) :
    (∃ u, rvCoprodLeftMap U.underlying.obj V.underlying.obj u = w) ∨
      (∃ v, rvCoprodRightMap U.underlying.obj V.underlying.obj v = w) := by
  rcases w.property with ⟨u, hu⟩ | ⟨v, hv⟩
  · exact Or.inl ⟨u, Subtype.ext hu⟩
  · exact Or.inr ⟨v, Subtype.ext hv⟩

end IntegrationInACVF.Section7.HK
