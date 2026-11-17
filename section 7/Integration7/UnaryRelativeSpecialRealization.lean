module

public import IntegrationSection5.RelativeSpecial
public import IntegrationSection5.RelativeSpecialRestriction
public import Section5.ParameterExtension

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! In VF arity one, a relatively special map is an actual special
bijection over the original real base: there are no frozen VF parameters. -/

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

private def cast_special {A A' : DefSet (M := M) S 1 a} {B B' : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hA : A = A') (hB : B = B') : SpecialBijection A' B' := by
  cases hA
  cases hB
  exact T

private theorem cast_special_value {A A' : DefSet (M := M) S 1 a} {B B' : DefSet (M := M) S 1 b}
    (T : SpecialBijection A B) (hA : A = A') (hB : B = B') (p : A') :
    ((cast_special T hA hB).toMap p).val =
      (T.toMap ⟨p.val,by rw [hA]; exact p.property⟩).val := by
  cases hA
  cases hB
  rfl

private theorem unary_insert_identity (u : Fin 1 → VF (M := M)) (p : Point (M := M) 1 a) :
    coordinateInsert 0 u p = p := by
  refine Prod.ext ?_ rfl
  funext j
  change Function.update u (0 : Fin 1) (p.1 0) j = p.1 j
  have hj : j = 0 := Subsingleton.elim _ _
  subst j
  exact Function.update_self 0 (p.1 0) u

theorem specialRelative_unary_special
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (f : Map A B) (h : SpecialRelative f 0) :
    ∃ T : SpecialBijection A B, ∀ p, T.toMap p = f p := by
  obtain ⟨hi,hT⟩ := h
  let u : Fin 1 → VF (M := M) := fun _ => 0
  obtain ⟨T,hT⟩ := hT u
  have hRS : coordinateFibreBase S 0 u ⊆ S := by
    rintro x (hx | ⟨j,hj⟩)
    · exact hx
    · exact False.elim (j.property (Subsingleton.elim _ _))
  let T' := T.extendBase hRS
  have hA : extendBase (coordinateFibre A 0 u) hRS = A := by
    apply defSet_eq_of_carrier_eq
    ext p
    change coordinateInsert 0 u p ∈ carrier A ↔ p ∈ carrier A
    rw [unary_insert_identity]
  have hB : extendBase (coordinateFibre B 0 u) hRS = B := by
    apply defSet_eq_of_carrier_eq
    ext p
    change coordinateInsert 0 u p ∈ carrier B ↔ p ∈ carrier B
    rw [unary_insert_identity]
  refine ⟨cast_special T' hA hB,?_⟩
  intro p
  apply Subtype.ext
  rw [cast_special_value]
  change ((T.chain.extendBase hRS).toMap ⟨p.val,_⟩).val = (f p).val
  rw [T.chain.extendBase_apply]
  have hpF : coordinateInsert 0 u p.val ∈ carrier A := by
    rw [unary_insert_identity]
    exact p.property
  let q : coordinateFibre A 0 u := ⟨p.val,hpF⟩
  change (T.toMap q).val = (f p).val
  rw [hT]
  rw [coordinateFibreMap_apply]
  have hp : (⟨coordinateInsert 0 u p.val,hpF⟩ : A) = p := Subtype.ext (unary_insert_identity u p.val)
  rw [hp]
  refine Prod.ext ?_ rfl
  funext j
  exact congrArg (fun i => vfAt (f p).val i) (Subsingleton.elim 0 j)

end IntegrationInACVF.Section7
