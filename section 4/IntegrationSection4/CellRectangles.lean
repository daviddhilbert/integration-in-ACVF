import IntegrationSection4.RVClassGeometry
import IntegrationSection4.Cells

noncomputable section
set_option backward.isDefEq.respectTransparency false

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.CellRectangles

open Cells BalancedFibres GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem nonempty {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t : RV (M := M)} (h : CellData R f t) : R.Nonempty := by
  have hFirst : (first R).Nonempty := by
    rcases h.first_cell with ⟨a,ha⟩ | ⟨ho,_⟩
    · exact ⟨a,ha.symm ▸ (show a ∈ ({a} : Set (VF (M := M))) from rfl)⟩
    · obtain ⟨x,hx⟩ := RadiusPreparationGeometry.open_nonempty ho
      obtain ⟨a,ha,_⟩ := hx
      exact ⟨a,ha⟩
  obtain ⟨a,ha⟩ := hFirst
  obtain ⟨b,hb⟩ := translatedRV_nonempty t (f a)
  refine ⟨(a,b),?_⟩
  change b ∈ fibre R a
  rw [h.fibres a ha]
  exact hb

theorem rectangle_of_fibres (R : Set (VF (M := M) × VF (M := M)))
    (S : Set (VF (M := M))) (h : ∀ a ∈ first R, fibre R a = S) : R = first R ×ˢ S := by
  ext p
  constructor
  · intro hp
    have ha : p.1 ∈ first R := ⟨p,hp,rfl⟩
    exact ⟨ha,(h p.1 ha) ▸ hp⟩
  · rintro ⟨ha,hb⟩
    change p.2 ∈ fibre R p.1
    rw [h p.1 ha]
    exact hb

theorem translated_open (t : RV (M := M)) (ht : t ≠ rv (0 : VF (M := M))) (c : VF (M := M)) :
    PaperBalls.IsOpenBall (rawSet (translatedRV t c)) := by
  obtain ⟨x,hx⟩ := translatedRV_nonempty t c
  rw [TranslatedRVGeometry.ordinary_ball t ht c x hx]
  exact Or.inr ⟨_,_,rfl⟩

theorem raw_image (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) :
    rawSet (f '' D) = rawMap f '' rawSet D := by
  ext y
  constructor
  · rintro ⟨z,⟨a,ha,rfl⟩,he⟩
    exact ⟨a.val,⟨a,ha,rfl⟩,(rawMap_on f a).trans he⟩
  · rintro ⟨_,⟨a,ha,rfl⟩,he⟩
    exact ⟨f a,⟨a,ha,rfl⟩,(rawMap_on f a).symm.trans he⟩

/-- The precise nonbalanced shape following 4.7, including the allowed
singleton first 1-cell. If the first projection is open, this is an open
polydisc. The unqualified printed statement has a singleton boundary. -/
theorem rectangle (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (h : CellData R f t) (ht : t ≠ rv (0 : VF (M := M)))
    (hNot : ¬ ∃ u, IsBalanced R f u t) :
    ∃ S : Set (VF (M := M)), PaperBalls.IsOpenBall (rawSet S) ∧ R = first R ×ˢ S := by
  obtain ⟨p₀,hp₀⟩ := nonempty h
  let a₀ := p₀.1
  have ha₀ : a₀ ∈ first R := ⟨p₀,hp₀,rfl⟩
  have finish (hFib : ∀ a ∈ first R, fibre R a = translatedRV t (f a₀)) :
      ∃ S : Set (VF (M := M)), PaperBalls.IsOpenBall (rawSet S) ∧ R = first R ×ˢ S :=
    ⟨translatedRV t (f a₀),translated_open t ht (f a₀),rectangle_of_fibres R _ hFib⟩
  have const (hc : ∀ a ∈ first R, ∀ b ∈ first R, f a = f b) :
      ∃ S : Set (VF (M := M)), PaperBalls.IsOpenBall (rawSet S) ∧ R = first R ×ˢ S := by
    apply finish
    intro a ha
    rw [h.fibres a ha,hc a ha a₀ ha₀]
  rcases h.positioning with hc | ⟨hInj,hOO,r,hr,htr⟩ | ⟨u,hu⟩
  · exact const hc
  · rcases h.first_cell with ⟨a,ha⟩ | ⟨hDo,_⟩
    · apply const
      intro x hx y hy
      rw [ha] at hx hy
      exact congrArg f (hx.trans hy.symm)
    · have hE : PaperBalls.IsOpenBall (rawSet (f '' first R)) :=
        (raw_image (first R) f).symm ▸ ((hOO _ Set.Subset.rfl).mp hDo)
      rcases hE with hWhole | ⟨c,β,hE⟩
      · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inl ⟨hWhole,rfl⟩)
        rw [he] at htr
        exact (WithBot.not_coe_le_bot _ htr).elim
      · have he := PaperBallInvariants.hasRadius_unique δ hδ hr
          (Or.inr (Or.inr ⟨c,β,true,hE,rfl⟩))
        rw [he] at htr
        have hβ : Values.vrv t ≤ β.val := WithBot.coe_le_coe.mp htr
        have haI : (f a₀).val ∈ gammaBall c β true := hE ▸
          (show (f a₀).val ∈ rawSet (f '' first R) from ⟨f a₀,⟨a₀,ha₀,rfl⟩,rfl⟩)
        apply finish
        intro a ha
        have haJ : (f a).val ∈ gammaBall c β true := hE ▸
          (show (f a).val ∈ rawSet (f '' first R) from ⟨f a,⟨a,ha,rfl⟩,rfl⟩)
        have hgt := GammaDifferenceRealization.difference_gt_radius c β (f a₀) (f a) haI haJ
        let γ : Values.Gamma (M := M) := ⟨Values.vrv t,TranslatedRVGeometry.value_ne_infinity t ht⟩
        have hClose := TranslatedRVGeometry.mem_of_value_gt (f a₀) (f a) γ (lt_of_le_of_lt hβ hgt)
        exact (h.fibres a ha).trans (RVClassGeometry.centres_close t ht (f a₀) (f a) hClose)
  · exact (hNot ⟨u,hu⟩).elim

theorem open_polydisc (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)} {t : RV (M := M)}
    (h : CellData R f t) (ht : t ≠ rv (0 : VF (M := M)))
    (hNot : ¬ ∃ u, IsBalanced R f u t) (hFirst : PaperBalls.IsOpenBall (rawSet (first R))) :
    ∃ D E : Set (VF (M := M)), R = D ×ˢ E ∧
      PaperBalls.IsOpenBall (rawSet D) ∧ PaperBalls.IsOpenBall (rawSet E) := by
  obtain ⟨S,hS,hR⟩ := rectangle δ hδ h ht hNot
  exact ⟨first R,S,hR,hFirst,hS⟩

end IntegrationInACVF.Section4.CellRectangles
