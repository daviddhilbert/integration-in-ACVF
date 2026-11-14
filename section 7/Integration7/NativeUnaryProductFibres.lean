import Integration7.NativeUnaryProductMaps

/-! Coordinate fibres of actual unary products, and the exact fibre map
of the first-factor action, including empty frozen-coordinate fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m r : ℕ}

theorem native_unary_product_coordinate_fibre
    (A : DefSet (M := M) S 1 m) (B : DefSet (M := M) S 1 0)
    (u : Fin 2 → VF (M := M)) (p : Point (M := M) 1 m) :
    p ∈ carrier (coordinateFibre (nativeUnaryProductDomain A B) 0 u) ↔
      p ∈ carrier A ∧ ((fun _ : Fin 1 => u 1),Fin.elim0) ∈ carrier B := by
  change coordinateInsert 0 u p ∈ carrier (nativeUnaryProductDomain A B) ↔ _
  rw [native_unary_product_carrier,coordinateProject_insert]
  simp only [coordinateInsert,vfAt,Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]

theorem native_unary_product_fibre_map_value
    {A : DefSet (M := M) S 1 m} {D : DefSet (M := M) S 1 r}
    (f : Map A D) (B : DefSet (M := M) S 1 0)
    (u : Fin 2 → VF (M := M)) (p : coordinateFibre (nativeUnaryProductDomain A B) 0 u) :
    (coordinateFibreMap (nativeUnaryProductMap f B) 0 (native_unary_product_map_relative f B) u p).val =
      (f ⟨p.val,((native_unary_product_coordinate_fibre A B u p.val).mp p.property).1⟩).val := by
  let q : nativeUnaryProductDomain A B := ⟨coordinateInsert 0 u p.val,p.property⟩
  let a : A := ⟨p.val,((native_unary_product_coordinate_fibre A B u p.val).mp p.property).1⟩
  have hqa : nativeUnaryProductLeftMap A B q = a := Subtype.ext (coordinateProject_insert 0 u p.val)
  have h := congrArg Subtype.val (native_unary_product_map_left f B q)
  rw [hqa] at h
  rw [coordinateFibreMap_apply]
  exact h

end IntegrationInACVF.Section7
