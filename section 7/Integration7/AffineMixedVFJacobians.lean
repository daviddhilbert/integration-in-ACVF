import Integration7.VFVolumeBijections

/-! Any defined mixed Jacobian of a map whose VF values are affine on
the fixed-label fibre equals the determinant of that affine linear map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a b : ℕ}

theorem mixed_vf_jacobian_eq_of_affine_vf
    {A : Set ((Fin n → VFType (M := M)) × (Fin a → CanonicalRV.RVSort M))}
    {B : Set ((Fin n → VFType (M := M)) × (Fin b → CanonicalRV.RVSort M))}
    (f : A → B) (p : A) (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (c : Fin n → VFType (M := M))
    (h : ∀ q, q.val.2 = p.val.2 → (f q).val.1 = L q.val.1+c) {J : VFType (M := M)}
    (hJ : HasMixedVFJacobianAt f p J) : J = (LinearMap.toMatrix' L).det := by
  obtain ⟨F,⟨ρ,hF⟩,hJF⟩ := hJ
  have he : Set.EqOn F (fun z => L z+c) (vfBall p.val.1 ρ) := by
    intro z hz
    obtain ⟨hp,hpF⟩ := hF z hz
    exact (congrArg Prod.fst hpF).symm.trans (h ⟨(z,p.val.2),hp⟩ rfl)
  exact (hJF.congr_on_vfBall he).unique (hasVFDerivativeAt_affine L c p.val.1).hasJacobianAt

end IntegrationInACVF.Section7
