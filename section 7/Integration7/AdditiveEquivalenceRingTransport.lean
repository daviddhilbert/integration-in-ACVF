module

public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Ring.Equiv

@[expose] public section

/-! Ring transport through an additive equivalence retains the original
addition, zero, negation and integer scalar multiplication. -/
noncomputable section
namespace IntegrationInACVF.Section7
universe u v
variable {A : Type u} [AddCommGroup A] {R : Type v} [Ring R]

def ringOfAdditiveEquivalence (e : A ≃+ R) : Ring A := by
  letI : One A := ⟨e.symm 1⟩
  letI : Mul A := ⟨fun x y => e.symm (e x*e y)⟩
  letI : Pow A ℕ := ⟨fun x n => e.symm (e x^n)⟩
  letI : NatCast A := ⟨fun n => e.symm (n : R)⟩
  letI : IntCast A := ⟨fun n => e.symm (n : R)⟩
  exact e.injective.ring e e.map_zero (e.apply_symm_apply 1) e.map_add
    (fun x y => e.apply_symm_apply (e x*e y)) e.map_neg e.map_sub
    (fun n x => map_nsmul e n x) (fun n x => map_zsmul e n x)
    (fun x n => e.apply_symm_apply (e x^n))
    (fun n => e.apply_symm_apply (n : R)) (fun n => e.apply_symm_apply (n : R))

def ringEquivOfAdditiveEquivalence (e : A ≃+ R) :
    letI := ringOfAdditiveEquivalence e
    A ≃+* R := by
  letI := ringOfAdditiveEquivalence e
  exact { e with map_mul' := fun x y => e.apply_symm_apply (e x*e y) }
end IntegrationInACVF.Section7
