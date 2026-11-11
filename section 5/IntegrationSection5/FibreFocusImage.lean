import IntegrationSection5.FibreFocus

/-! The target of the restricted focus is the actual coordinate fibre of
the global focus image. -/
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

theorem fibreFocus_image_carrier (D : Focus A i k) (u : Fin n → VF (M := M)) :
    carrier (fibreFocus D u).etaImage = carrier (coordinateFibre D.etaImage i u) := by
  ext q
  constructor
  · rintro ⟨p,hp⟩
    change ∃ a : A, D.toFocusGeometry.eta a.val = coordinateInsert i u q
    refine ⟨⟨coordinateInsert i u p.val,p.property⟩,?_⟩
    have h := fibreFocusGeometry_eta_insert D u p
    exact h.symm.trans (congrArg (coordinateInsert i u) hp)
  · intro hq
    obtain ⟨a,ha⟩ := hq
    have hOther : ∀ j, j ≠ i → vfAt a.val j = u j := by
      intro j hj
      have h := congrArg (fun z : Point (M := M) n m => vfAt z j) ha
      exact (D.toFocusGeometry.eta_other a.val j hj).symm.trans
        (h.trans (coordinateInsert_other i u q j hj))
    have hRestore := coordinateInsert_project i u a.val hOther
    let p : coordinateFibre A i u := ⟨coordinateProject i a.val,by
      change coordinateInsert i u (coordinateProject i a.val) ∈ carrier A
      rw [hRestore]
      exact a.property⟩
    refine ⟨p,?_⟩
    apply coordinateInsert_injective i u
    have h := fibreFocusGeometry_eta_insert D u p
    exact h.trans ((congrArg D.toFocusGeometry.eta hRestore).trans ha)

theorem fibreFocus_image_eq (D : Focus A i k) (u : Fin n → VF (M := M)) :
    (fibreFocus D u).etaImage = coordinateFibre D.etaImage i u := by
  cases hX : (fibreFocus D u).etaImage with
  | mk X hXdef =>
    cases hY : coordinateFibre D.etaImage i u with
    | mk Y hYdef =>
      have h : X = Y := by simpa only [hX,hY] using fibreFocus_image_carrier D u
      subst Y
      rfl

def specialCastTarget {R : Set M} {a b c : ℕ} {X : DefSet (M := M) R a b}
    {Y Z : DefSet (M := M) R a c} (T : SpecialBijection X Y) (h : Y = Z) :
    SpecialBijection X Z := h ▸ T

theorem specialCastTarget_val {R : Set M} {a b c : ℕ} {X : DefSet (M := M) R a b}
    {Y Z : DefSet (M := M) R a c} (T : SpecialBijection X Y) (h : Y = Z) (p : X) :
    ((specialCastTarget T h).toMap p).val = (T.toMap p).val := by
  subst Z
  rfl

def fibreCentripetal (D : Focus A i k) (u : Fin n → VF (M := M)) :
    SpecialBijection (coordinateFibre A i u) (coordinateFibre D.etaImage i u) :=
  specialCastTarget (SpecialBijection.centripetal (fibreFocus D u)) (fibreFocus_image_eq D u)

theorem fibreCentripetal_apply (D : Focus A i k) (u : Fin n → VF (M := M))
    (p : coordinateFibre A i u) :
    coordinateInsert i u (fibreCentripetal D u |>.toMap p).val =
      D.toFocusGeometry.eta (coordinateInsert i u p.val) := by
  unfold fibreCentripetal
  rw [specialCastTarget_val]
  exact fibreFocusGeometry_eta_insert D u p

end IntegrationInACVF.Section5
