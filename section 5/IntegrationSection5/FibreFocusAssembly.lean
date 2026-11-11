import IntegrationSection5.FibreFocusImage
import IntegrationSection5.RelativeFibreBijection

/-! Assemble a definable map from actual unary fibre foci, retaining its
actual image and full pointwise equality on each coordinate fibre. -/
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
variable {S : Set M} {n m : ℕ} {A : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

theorem fibreFocus_map_image_carrier (f : Map A (PresentedSet.univ (pointSpace n m) S))
    (hi : UnaryRelative (Map.toImage f) i)
    (F : ∀ u : Fin n → VF (M := M), Focus (coordinateFibre A i u) 0 k)
    (hF : ∀ u (p : coordinateFibre A i u), coordinateInsert i u ((F u).toFocusGeometry.eta p.val) =
      (f ⟨coordinateInsert i u p.val,p.property⟩).val)
    (u : Fin n → VF (M := M)) :
    carrier (F u).etaImage = carrier (coordinateFibre (Map.image f) i u) := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    change ∃ a : A, (f a).val = coordinateInsert i u q
    exact ⟨⟨coordinateInsert i u p.val,p.property⟩,(hF u p).symm.trans (congrArg (coordinateInsert i u) hp)⟩
  · rintro ⟨a,ha⟩
    have hOther : ∀ j, j ≠ i → vfAt a.val j = u j := by
      intro j hj
      have h := congrArg (fun z : Point (M := M) n m => vfAt z j) ha
      exact (hi a j hj).symm.trans (h.trans (coordinateInsert_other i u q j hj))
    have hRestore := coordinateInsert_project i u a.val hOther
    let p : coordinateFibre A i u := ⟨coordinateProject i a.val,by
      change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
      rw [hRestore]
      exact a.property⟩
    have hax : (⟨coordinateInsert i u p.val,p.property⟩ : A) = a := Subtype.ext hRestore
    refine ⟨p,?_⟩
    apply coordinateInsert_injective i u
    exact (hF u p).trans ((congrArg (fun z : A => (f z).val) hax).trans ha)

theorem specialRelative_of_fibre_focus (f : Map A (PresentedSet.univ (pointSpace n m) S))
    (hi : UnaryRelative (Map.toImage f) i)
    (F : ∀ u : Fin n → VF (M := M), Focus (coordinateFibre A i u) 0 k)
    (hF : ∀ u (p : coordinateFibre A i u), coordinateInsert i u ((F u).toFocusGeometry.eta p.val) =
      (f ⟨coordinateInsert i u p.val,p.property⟩).val) : SpecialRelative (Map.toImage f) i := by
  refine ⟨hi,?_⟩
  intro u
  have hEq : (F u).etaImage = coordinateFibre (Map.image f) i u := by
    cases hX : (F u).etaImage with
    | mk X hXdef =>
      cases hY : coordinateFibre (Map.image f) i u with
      | mk Y hYdef =>
        have h : X = Y := by simpa only [hX,hY] using fibreFocus_map_image_carrier f hi F hF u
        subst Y
        rfl
  refine ⟨specialCastTarget (SpecialBijection.centripetal (F u)) hEq,?_⟩
  intro p
  apply Subtype.ext
  apply coordinateInsert_injective i u
  rw [specialCastTarget_val,coordinateFibreMap_insert]
  exact hF u p

end IntegrationInACVF.Section5
