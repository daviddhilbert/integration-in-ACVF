import Integration7.UnaryRelativeSpecialRealization

/-! A unary special bijection is relatively special in its unique VF
coordinate. No choice of additional frozen parameters is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {a b : ℕ}

private theorem unary_insert (u : Fin 1 → VF (M := M)) (p : Point (M := M) 1 a) :
    coordinateInsert 0 u p = p := by
  refine Prod.ext ?_ rfl
  funext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Function.update_self 0 (p.1 0) u

private def cast_special {A A' : DefSet (M := M) S 1 a} {D D' : DefSet (M := M) S 1 b}
    (T : SpecialBijection A D) (hA : A = A') (hD : D = D') : SpecialBijection A' D' := by
  cases hA
  cases hD
  exact T

private theorem cast_special_value {A A' : DefSet (M := M) S 1 a} {D D' : DefSet (M := M) S 1 b}
    (T : SpecialBijection A D) (hA : A = A') (hD : D = D') (p : A') :
    ((cast_special T hA hD).toMap p).val = (T.toMap ⟨p.val,by rw [hA];exact p.property⟩).val := by
  cases hA
  cases hD
  rfl

theorem unary_special_relative {A : DefSet (M := M) S 1 a} {D : DefSet (M := M) S 1 b}
    (T : SpecialBijection A D) : SpecialRelative T.toMap 0 := by
  have hi : UnaryRelative T.toMap 0 := by
    intro p j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  refine ⟨hi,?_⟩
  intro u
  let hS : S ⊆ coordinateFibreBase S 0 u := Set.subset_union_left
  let T' := T.extendBase hS
  have hA : extendBase A hS = coordinateFibre A 0 u := by
    apply defSet_eq_of_carrier_eq
    ext p
    change p ∈ carrier A ↔ coordinateInsert 0 u p ∈ carrier A
    rw [unary_insert]
  have hD : extendBase D hS = coordinateFibre D 0 u := by
    apply defSet_eq_of_carrier_eq
    ext p
    change p ∈ carrier D ↔ coordinateInsert 0 u p ∈ carrier D
    rw [unary_insert]
  refine ⟨cast_special T' hA hD,?_⟩
  intro p
  apply Subtype.ext
  rw [cast_special_value]
  change ((T.chain.extendBase hS).toMap ⟨p.val,_⟩).val = _
  rw [T.chain.extendBase_apply,coordinateFibreMap_apply]
  have hp : (⟨coordinateInsert 0 u p.val,p.property⟩ : A) = ⟨p.val,by
      rw [← unary_insert u p.val];exact p.property⟩ := Subtype.ext (unary_insert u p.val)
  rw [hp]
  refine Prod.ext ?_ rfl
  funext j
  exact congrArg (fun i => vfAt (T.toMap ⟨p.val,_⟩).val i) (Subsingleton.elim j 0)

end IntegrationInACVF.Section7
