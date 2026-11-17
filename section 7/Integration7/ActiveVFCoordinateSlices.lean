module

public import Integration7.RelativeVFJacobianRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The active partial derivative is exactly the unary Jacobian on a
fixed complementary VF tuple. This is a pointwise chart assertion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ}
local notation "VF" => VFType (M := M)

def activeVFCoordinateSlice (f : (Fin n → VF) → Fin n → VF)
    (a : Fin n → VF) (i : Fin n) (x : Fin 1 → VF) : Fin 1 → VF :=
  fun _ => f (Function.update a i (x 0)) i

theorem active_vf_coordinate_slice_jacobian
    {f : (Fin n → VF) → Fin n → VF} {a : Fin n → VF} {i : Fin n} {J : VF}
    (hJ : HasVFPartialAt f a i i J) :
    HasVFJacobianAt (activeVFCoordinateSlice f a i) (fun _ => a i) J := by
  refine ⟨fun _ _ => J,?_,by simp⟩
  intro j k
  have hj : j = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst j k
  intro ε
  obtain ⟨δ,hδ⟩ := hJ ε
  refine ⟨δ,fun t ht hnear => ?_⟩
  have he : Function.update a i (a i + t) = a + Pi.single i t := by
    funext j
    by_cases hj : j = i
    · subst j
      simp
    · simp [Function.update_of_ne hj,Pi.single_eq_of_ne hj]
  change ε.val * Values.vfValueHom t < Values.vfValueHom
    (f (Function.update a i (a i + t)) i - f (Function.update a i (a i)) i - J * t)
  rw [he,Function.update_eq_self]
  exact hδ t ht hnear

theorem relative_vf_coordinate_slice_jacobian
    {f : (Fin n → VF) → Fin n → VF} {a : Fin n → VF} {J : VF}
    (hJ : HasVFJacobianAt f a J) (i : Fin n) (ρ : Values.Gamma (M := M))
    (hfixed : ∀ x ∈ vfBall a ρ, ∀ j, j ≠ i → f x j = x j) :
    HasVFJacobianAt (activeVFCoordinateSlice f a i) (fun _ => a i) J :=
  active_vf_coordinate_slice_jacobian (vf_jacobian_active_partial hJ i ρ hfixed)

end IntegrationInACVF.Section7
