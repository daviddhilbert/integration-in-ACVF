import Integration7.IndependentHeadCoordinateFields
import Integration7.RelativeFibreTranslationVolumes

/-! A genuinely special preparation on every head fibre has full VF
Jacobian one almost everywhere. The frozen coordinates are included in
the actual unary coefficient field before applying the special-chain
derivative theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {n a b : ℕ}

set_option maxHeartbeats 1600000 in
theorem relative_head_special_defined_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (f : Map A B) (hSpecial : SpecialRelative f 0)
    (p : rawSpecialSet hc A)
    (hp : AlgebraicIndependent (vfParameterField (C.base : Set M)) p.val.1)
    {J : VFType (M := M)} (hJ : HasMixedVFJacobianAt (rawSpecialMap hc f) p J) :
    J = 1 := by
  letI : CharZero (VFType (M := M)) := vfCharZero_of_model00 C.model00
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  let u := headFrozenTuple (fun j : Fin n => p.val.1 j.succ)
  let z : Point (M := M) 1 a := (fun _ => p.val.1 0,p.val.2)
  have he : coordinateInsert 0 u z = p.val := by
    refine Prod.ext ?_ rfl
    funext j
    cases j using Fin.cases <;> rfl
  let q : rawSpecialSet hc (coordinateFibre A 0 u) := ⟨z,by
    change coordinateInsert 0 u z ∈ carrier A
    rw [he]
    exact p.property⟩
  have hsmall : Cardinal.mk (coordinateFibreBase (C.base : Set M) 0 u) < C.κ := by
    rw [head_coordinate_fibre_base]
    exact small_union_range C.uncountable.le (C.base : Set M) C.small
      (fun j : Fin n => (p.val.1 j.succ).val)
  have hq : AlgebraicIndependent
      (vfParameterField (coordinateFibreBase (C.base : Set M) 0 u)) q.val.1 :=
    independent_head_over_coordinate_fibre_base p.val.1 hp
  obtain ⟨hi,hT⟩ := hSpecial
  obtain ⟨T,hT⟩ := hT u
  have hMap : T.toMap = coordinateFibreMap f 0 hi u :=
    @SpecialTransformations.DefinableGeometry.Map.ext LRV M
      (@CanonicalStructure.normalize M sM) _ _ (coordinateFibreBase (C.base : Set M) 0 u)
      _ _ T.toMap (coordinateFibreMap f 0 hi u) hT
  obtain ⟨L,⟨F,hF,hDer⟩,hDet⟩ := specialChain_det_one_of_independent hc
    C.uncountable.le C.saturated hsmall Values.presentation_compatible T.chain q hq
  have hOne : HasMixedVFJacobianAt (rawSpecialMap hc (coordinateFibreMap f 0 hi u)) q 1 := by
    rw [← hMap]
    exact ⟨F,hF,by simpa only [hDet] using hDer.hasJacobianAt⟩
  have hPoint : (⟨coordinateInsert 0 u q.val,q.property⟩ : rawSpecialSet hc A) = p :=
    Subtype.ext he
  have hJ' : HasMixedVFJacobianAt (rawSpecialMap hc f)
      ⟨coordinateInsert 0 u q.val,q.property⟩ J := hPoint.symm ▸ hJ
  exact (relative_mixed_vf_jacobian_on_coordinate_fibre hc f 0 hi u q J hJ').unique hOne

set_option maxHeartbeats 1600000 in
theorem relative_head_special_vf_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) (n+1) a}
    {B : DefSet (M := M) (C.base : Set M) (n+1) b}
    (f : Map A B) (hSpecial : SpecialRelative f 0) :
    VFAlmostEverywhere (rawSpecialSet hc A)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1) := by
  letI : CharZero (VFType (M := M)) := vfCharZero_of_model00 C.model00
  letI : Valued (VFType (M := M)) (Values.presentationType (M := M)) :=
    Valued.mk' Values.presentationValuation
  obtain ⟨D,hDA,hD,hJac⟩ := exists_mixedJacobianOne_exception hc C.saturated C.small
    (Nat.zero_lt_succ n) (rawSpecialMap hc f) (by
      intro p hp
      obtain ⟨L,F,hF,hDer⟩ := mixedDifferentiableAt_of_independent hc C.uncountable.le
        C.saturated C.small Values.presentation_compatible (rawSpecialMap hc f) p hp
      exact ⟨L,⟨F,hF,hDer⟩,relative_head_special_defined_jacobian_one hc C f hSpecial p hp
        ⟨F,hF,hDer.hasJacobianAt⟩⟩)
  exact ⟨D,hDA,hD,hJac⟩

end IntegrationInACVF.Section7
