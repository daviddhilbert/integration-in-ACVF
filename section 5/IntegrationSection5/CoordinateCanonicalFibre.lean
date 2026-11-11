import IntegrationSection5.CoordinateCanonical

/-! Actual unary canonical special witnesses on the fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n m : ℕ}

theorem coordinateCanonical_fibre_carrier (A : DefSet (M := M) S n m) (i : Fin n)
    (u : Fin n → VF (M := M)) :
    carrier (canonicalImage (coordinateFibre A i u)) =
      carrier (coordinateFibre (coordinateCanonicalImage A i) i u) := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    change ∃ a : A, coordinateCanonical i a.val = coordinateInsert i u q
    refine ⟨⟨coordinateInsert i u p.val,p.property⟩,?_⟩
    exact (coordinateInsert_canonical i u p.val).symm.trans (congrArg (coordinateInsert i u) hp)
  · rintro ⟨a,ha⟩
    have hOther : ∀ j, j ≠ i → vfAt a.val j = u j := by
      intro j hj
      exact (congrArg (fun z : Point (M := M) n (1+m) => vfAt z j) ha).trans
        (coordinateInsert_other i u q j hj)
    have hRestore := coordinateInsert_project i u a.val hOther
    let p : coordinateFibre A i u := ⟨coordinateProject i a.val,by
      change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
      rw [hRestore]
      exact a.property⟩
    refine ⟨p,?_⟩
    apply coordinateInsert_injective i u
    exact (coordinateInsert_canonical i u p.val).trans
      ((congrArg (coordinateCanonical i) hRestore).trans ha)

theorem coordinateCanonical_fibre_eq (A : DefSet (M := M) S n m) (i : Fin n)
    (u : Fin n → VF (M := M)) :
    canonicalImage (coordinateFibre A i u) =
      coordinateFibre (coordinateCanonicalImage A i) i u := by
  cases hX : canonicalImage (coordinateFibre A i u) with
  | mk X hXdef =>
    cases hY : coordinateFibre (coordinateCanonicalImage A i) i u with
    | mk Y hYdef =>
      have h : X = Y := by simpa only [hX,hY] using coordinateCanonical_fibre_carrier A i u
      subst Y
      rfl

def coordinateCanonicalFibre (A : DefSet (M := M) S n m) (i : Fin n)
    (u : Fin n → VF (M := M)) :
    SpecialBijection (coordinateFibre A i u) (coordinateFibre (coordinateCanonicalImage A i) i u) :=
  specialCastTarget (SpecialBijection.canonical (coordinateFibre A i u)) (coordinateCanonical_fibre_eq A i u)

theorem coordinateCanonical_specialRelative (A : DefSet (M := M) S n m) (i : Fin n) :
    SpecialRelative (coordinateCanonicalBijection A i) i := by
  refine ⟨coordinateCanonical_unaryRelative A i,fun u => ⟨coordinateCanonicalFibre A i u,?_⟩⟩
  intro p
  apply Subtype.ext
  apply coordinateInsert_injective i u
  rw [coordinateFibreMap_insert]
  unfold coordinateCanonicalFibre
  rw [specialCastTarget_val]
  exact coordinateInsert_canonical i u p.val

end IntegrationInACVF.Section5
