import Integration7.ActiveVFCoordinateSlices
import IntegrationSection5.RelativeFibreMaps
import Section9.SpecialJacobianGeneric

/-! A defined mixed VF Jacobian of a relatively unary map restricts to
the identical unary Jacobian on its actual coordinate fibre. The full
chart, source membership and fixed output RV labels are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

set_option maxHeartbeats 1600000 in
theorem relative_mixed_vf_jacobian_on_coordinate_fibre
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : DefSet (M := M) S n a} {B : DefSet (M := M) S n b}
    (f : Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (u : Fin n → VF (M := M))
    (p : rawSpecialSet hc (coordinateFibre A i u)) (J : VF (M := M))
    (hJ : HasMixedVFJacobianAt (rawSpecialMap hc f)
      ⟨coordinateInsert i u p.val,p.property⟩ J) :
    HasMixedVFJacobianAt (rawSpecialMap hc (coordinateFibreMap f i hi u)) p J := by
  let q : A := ⟨coordinateInsert i u p.val,p.property⟩
  let qa : Fin n → VFType (M := M) := q.val.1
  obtain ⟨F,⟨ρ,hF⟩,hJF⟩ := hJ
  have hfixed : ∀ x ∈ vfBall q.val.1 ρ, ∀ j, j ≠ i → F x j = x j := by
    intro x hx j hj
    obtain ⟨hxA,hFx⟩ := hF x hx
    exact (congrArg (fun y => y.1 j) hFx).symm.trans (hi ⟨(x,q.val.2),hxA⟩ j hj)
  let G := activeVFCoordinateSlice F q.val.1 i
  have hGJ : HasVFJacobianAt G p.val.1 J := by
    have h := relative_vf_coordinate_slice_jacobian hJF i ρ hfixed
    have he : (fun _ : Fin 1 => q.val.1 i) = p.val.1 := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact Function.update_self i _ u
    rw [he] at h
    exact h
  refine ⟨G,⟨ρ,?_⟩,hGJ⟩
  intro z hz
  let w : Fin n → VFType (M := M) := Function.update qa i (z 0)
  have hw : w ∈ vfBall qa ρ := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [w,qa,q,coordinateInsert,vfAt,Function.update_self] using hz 0
    · have hsame : w j = qa j := Function.update_of_ne hj _ _
      change ρ.val < Values.vfValueHom (M := M) (w j - qa j)
      rw [hsame,sub_self]
      exact gamma_lt_value_zero _
  obtain ⟨hwA,hFw⟩ := hF w hw
  have hrestore : (w,q.val.2) = coordinateInsert i u (z,p.val.2) := by
    refine Prod.ext ?_ rfl
    change Function.update (Function.update u i (p.val.1 0)) i (z 0) = Function.update u i (z 0)
    exact Function.update_idem _ _ _
  have hpz : coordinateInsert i u (z,p.val.2) ∈ carrier A := by
    rw [← hrestore]
    exact hwA
  have harg : (⟨coordinateInsert i u (z,p.val.2),hpz⟩ : A) = ⟨(w,q.val.2),hwA⟩ :=
    Subtype.ext hrestore.symm
  refine ⟨hpz,?_⟩
  change (coordinateFibreMap f i hi u ⟨(z,p.val.2),hpz⟩).val =
    (G z,(coordinateFibreMap f i hi u p).val.2)
  rw [coordinateFibreMap_apply]
  refine Prod.ext ?_ ?_
  · funext j
    change (f ⟨coordinateInsert i u (z,p.val.2),hpz⟩).val.1 i = F w i
    rw [harg]
    exact congrArg (fun y => y.1 i) hFw
  · change (f ⟨coordinateInsert i u (z,p.val.2),hpz⟩).val.2 = (f q).val.2
    rw [harg]
    have hlabels := congrArg (fun y : (Fin n → VFType (M := M)) × (Fin b → CanonicalRV.RVSort M) => y.2) hFw
    exact hlabels

end IntegrationInACVF.Section7
