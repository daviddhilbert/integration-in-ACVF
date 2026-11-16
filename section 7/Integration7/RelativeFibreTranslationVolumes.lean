module

public import Integration7.AffineMixedVFJacobians
public import Integration7.RelativeMixedFibreJacobians

@[expose] public section

/-! Actual relatively unary translations along frozen coordinate fibres
have Jacobian one almost everywhere and preserve every transported density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.DefinableGeometry.Space.ofEmbedding
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

set_option maxHeartbeats 1600000 in
theorem relative_fibre_translation_defined_jacobian
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (c : (Fin n → VF (M := M)) → (Fin a → RV (M := M)) → VF (M := M))
    (hTrans : ∀ u, ∀ q : coordinateFibre A i u,
      (coordinateFibreMap f i hi u q).val.1 0 = (show VFType (M := M) from q.val.1 0)-c u q.val.2)
    (p : rawSpecialSet hc A) {J : VFType (M := M)}
    (hJ : HasMixedVFJacobianAt (rawSpecialMap hc f) p J) : J = 1 := by
  let u := p.val.1
  let z : Point (M := M) 1 a := (fun _ => u i,p.val.2)
  have he : coordinateInsert i u z = p.val := by
    refine Prod.ext ?_ rfl
    funext j
    by_cases hj : j = i
    · subst j; exact Function.update_self i _ u
    · exact Function.update_of_ne hj _ _
  let q : rawSpecialSet hc (coordinateFibre A i u) := ⟨z,by
    change coordinateInsert i u z ∈ carrier A
    rw [he]
    exact p.property⟩
  have hp : (⟨coordinateInsert i u q.val,q.property⟩ : rawSpecialSet hc A) = p := Subtype.ext he
  have hJ' : HasMixedVFJacobianAt (rawSpecialMap hc f)
      ⟨coordinateInsert i u q.val,q.property⟩ J := hp.symm ▸ hJ
  have hSlice := relative_mixed_vf_jacobian_on_coordinate_fibre hc f i hi u q J hJ'
  have hdet := mixed_vf_jacobian_eq_of_affine_vf
    (rawSpecialMap hc (coordinateFibreMap f i hi u)) q LinearMap.id (fun _ : Fin 1 => -c u q.val.2)
    (by
      intro w hRV
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change (coordinateFibreMap f i hi u w).val.1 0 = w.val.1 0+ -c u q.val.2
      simpa only [hRV,sub_eq_add_neg] using hTrans u w) hSlice
  simpa only [LinearMap.toMatrix'_id,Matrix.det_one] using hdet

set_option maxHeartbeats 1600000 in
theorem relative_fibre_translation_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (M := M) (C.base : Set M) n a} {B : DefSet (M := M) (C.base : Set M) n b}
    (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (c : (Fin n → VF (M := M)) → (Fin a → RV (M := M)) → VF (M := M))
    (hTrans : ∀ u, ∀ q : coordinateFibre A i u,
      (coordinateFibreMap f i hi u q).val.1 0 = (show VFType (M := M) from q.val.1 0)-c u q.val.2) :
    VFAlmostEverywhere (rawSpecialSet hc A) (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1) := by
  letI : CharZero (VFType (M := M)) := IntegrationInACVF.Section6.vfCharZero_of_model00 C.model00
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  obtain ⟨D,hDA,hD,hJac⟩ := exists_mixedJacobianOne_exception hc C.saturated C.small hn (rawSpecialMap hc f) (by
    intro p hp
    obtain ⟨L,hL⟩ := mixedDifferentiableAt_of_independent hc C.uncountable.le C.saturated C.small
      Values.presentation_compatible (rawSpecialMap hc f) p hp
    obtain ⟨F,hF,hDer⟩ := hL
    exact ⟨L,⟨F,hF,hDer⟩,relative_fibre_translation_defined_jacobian hc f i hi c hTrans p
      ⟨F,hF,hDer.hasJacobianAt⟩⟩)
  exact ⟨D,hDA,hD,hJac⟩

theorem relative_fibre_translation_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (M := M) (C.base : Set M) n a} {B : DefSet (M := M) (C.base : Set M) n b}
    (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (c : (Fin n → VF (M := M)) → (Fin a → RV (M := M)) → VF (M := M))
    (hTrans : ∀ u, ∀ q : coordinateFibre A i u,
      (coordinateFibreMap f i hi u q).val.1 0 = (show VFType (M := M) from q.val.1 0)-c u q.val.2)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hDensity : ∀ p, ω.value p = π.value (rawSpecialMap hc f p)) :
    PreservesVFVolume ω π (rawSpecialMap hc f) :=
  (relative_fibre_translation_jacobian_one hc C hn f i hi c hTrans).mono
    (fun p hJ => ⟨1,hJ,by rw [RVOperations.rv_one,mul_one]; exact hDensity p⟩)

end IntegrationInACVF.Section7
