import IntegrationSection5.MatchedFocusContractibility

/-! A focus refines a contractible map when its marked zero points have
degenerate source RV cells. This is the reverse part of the focus argument. -/

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

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l r : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {C : DefSet (M := M) S 1 r} {k : Fin m}

theorem contractible_comp (f : A → B) (g : B → C)
    (hf : Contractible f) (hg : Contractible g) : Contractible (g ∘ f) :=
  fun a b hab => hg (f a) (f b) (hf a b hab)

theorem focus_post_contractible (H : Map C A) (hc : Contractible H) (ho : CellwiseOpenMap H)
    (hC : IsRVPullback (carrier C)) (D : Focus A 0 k)
    (hzero : ∀ a : C, (H a).val ∈ D.locus →
      vfAt (H a).val 0 = D.center (H a).val → vfAt a.val 0 = 0) :
    Contractible (Map.comp (SpecialBijection.centripetal D).toMap H) := by
  intro a b hab
  let c := focusClassShift D (H a)
  have hHab := hc a b hab
  by_cases hc0 : c = 0
  · change SameRV (D.toFocusGeometry.eta (H a).val) (D.toFocusGeometry.eta (H b).val)
    rw [unary_focus_eta_eq_shift D (H a) (H a) rfl,
      unary_focus_eta_eq_shift D (H a) (H b) hHab]
    change SameRV (unaryShift c (H a).val) (unaryShift c (H b).val)
    rw [hc0, unaryShift_zero, unaryShift_zero]
    exact hHab
  · have hact : (H a).val ∈ D.locus := by
      by_contra h
      exact hc0 (by simp [c, focusClassShift, h])
    by_cases ha0 : vfAt a.val 0 = 0
    · have he : a = b := Subtype.ext (eq_of_sameRV_of_zero hab ha0)
      subst b
      rfl
    · let E := (SpecialBijection.refl C).inverseFibre a
      have hE : IsUnaryOpenPolydisc E := ((SpecialBijection.refl C).remark_5_3 hC a ha0).1
      have hEC : E ⊆ carrier C := by
        rintro p ⟨x, he, hx⟩
        exact he ▸ x.property
      have hcell : ∀ p ∈ E, SameRV p a.val := by
        rintro p ⟨x, rfl, hx⟩
        exact hx
      let g := Map.comp (SpecialBijection.centripetal D).toMap H
      have hgo : CellwiseOpenMap g := cellwiseOpenMap_comp H
        (SpecialBijection.centripetal D).toMap hc ho (focus_primitive_open_images D)
      have hImage := hgo E hE hEC ⟨a, hcell⟩
      have haE : a.val ∈ E := ⟨a, rfl, rfl⟩
      have hbE : b.val ∈ E := ⟨b, rfl, hab.symm⟩
      apply unary_open_polydisc_sameRV hImage ?_ ⟨a, haE, rfl⟩ ⟨b, hbE, rfl⟩
      rintro z ⟨x, hx, rfl⟩ hz
      have hxa := hcell x.val hx
      have hactx := (mem_iff_sameRV D.locus_pullback (hc a x hxa.symm)).mp hact
      change vfAt (D.toFocusGeometry.eta (H x).val) 0 = 0 at hz
      rw [FocusGeometry.eta, ite_eq_left hactx] at hz
      change vfAt (H x).val 0 - D.center (H x).val = 0 at hz
      exact ha0 ((sameRV_zero_iff hxa).mp (hzero x hactx (sub_eq_zero.mp hz)))

theorem focused_post_contractible (H : Map C A) (hc : Contractible H) (ho : CellwiseOpenMap H)
    (hC : IsRVPullback (carrier C)) (D : Focus A 0 k)
    (hzero : ∀ a : C, (H a).val ∈ D.locus →
      vfAt (H a).val 0 = D.center (H a).val → vfAt a.val 0 = 0) :
    Contractible (Map.comp (focussedCanonical D).toMap H) := by
  have hh := focus_post_contractible H hc ho hC D hzero
  exact contractible_comp (Map.comp (SpecialBijection.centripetal D).toMap H)
    (SpecialBijection.canonical D.etaImage).toMap hh (canonical_contractible D.etaImage)

end IntegrationInACVF.Section5
