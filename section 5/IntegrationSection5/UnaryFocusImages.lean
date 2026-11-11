import IntegrationSection5.FocusSection
import IntegrationSection5.UnaryOpenImages

/-! A unary focus is one fixed translation on each original RV cell. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 1 m} {k : Fin m}

theorem unary_focus_center_eq (D : Focus A 0 k) (a b : A)
    (ha : a.val ∈ D.locus) (hab : SameRV a.val b.val) : D.center a.val = D.center b.val := by
  have hb := (mem_iff_sameRV D.locus_pullback hab).mp ha
  apply D.independent a.val ⟨a.property, ha⟩ b.val ⟨b.property, hb⟩
  refine Prod.ext ?_ ((sameRV_iff _ _).mp hab).2
  funext i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [erase, replace]

def focusClassShift (D : Focus A 0 k) (a : A) : VF (M := M) :=
  if a.val ∈ D.locus then D.center a.val else 0

theorem unary_focus_eta_eq_shift (D : Focus A 0 k) (a b : A)
    (hab : SameRV a.val b.val) :
    D.toFocusGeometry.eta b.val = unaryShift (focusClassShift D a) b.val := by
  by_cases ha : a.val ∈ D.locus
  · have hb := (mem_iff_sameRV D.locus_pullback hab).mp ha
    have hc := unary_focus_center_eq D a b ha hab
    rw [FocusGeometry.eta, if_pos hb]
    refine Prod.ext ?_ rfl
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [replace, unaryShift, focusClassShift, ha, hc]
  · have hb : b.val ∉ D.locus := fun hb => ha ((mem_iff_sameRV D.locus_pullback hab).mpr hb)
    rw [FocusGeometry.eta, if_neg hb]
    refine Prod.ext ?_ rfl
    funext i
    simp [unaryShift, focusClassShift, ha]

theorem unary_focus_image_eq_shift (D : Focus A 0 k) (a : A)
    (E : Set (Point (M := M) 1 m)) (hEA : E ⊆ carrier A)
    (hcell : ∀ p ∈ E, SameRV p a.val) :
    unaryImage (SpecialBijection.centripetal D).toMap E = unaryShift (focusClassShift D a) '' E := by
  ext q
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨b.val, hb, ?_⟩
    exact (unary_focus_eta_eq_shift D a b (hcell b.val hb).symm).symm
  · rintro ⟨p, hp, he⟩
    let b : A := ⟨p, hEA hp⟩
    exact ⟨b, hp, (unary_focus_eta_eq_shift D a b (hcell p hp).symm).trans he⟩

theorem focus_primitive_open_images (D : Focus A 0 k) :
    CellwiseOpenMap (SpecialBijection.centripetal D).toMap := by
  intro E hE hEA hcell
  obtain ⟨a, ha⟩ := hcell
  rw [unary_focus_image_eq_shift D a E hEA ha]
  exact unaryShift_open_polydisc _ hE

def focussedCanonical (D : Focus A 0 k) : SpecialBijection A (canonicalImage D.etaImage) :=
  ⟨.cons (.centripetal D) (.cons (.canonical D.etaImage) (.nil _)), by decide, by decide, trivial⟩

theorem focussedCanonical_vf (D : Focus A 0 k) (a : A) :
    (focussedCanonical D).toMap a |>.val.1 = (D.toFocusGeometry.eta a.val).1 := rfl

end IntegrationInACVF.Section5
