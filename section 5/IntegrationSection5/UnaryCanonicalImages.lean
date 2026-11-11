import IntegrationSection5.UnaryOpenImages

/-! Canonical tagging preserves RV classes and open images on one RV cell. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section5

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {m l k : ℕ}
variable {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l}
variable {C : DefSet (M := M) S 1 k}

theorem canonical_contractible (A : DefSet (M := M) S 1 m) :
    Contractible (SpecialBijection.canonical A).toMap := by
  intro a b hab
  exact (canonical_sameRV_iff a.val b.val).mpr hab

theorem canonical_eq_reframe {p q : Point (M := M) 1 m} (h : SameRV p q) :
    canonical p = unaryReframe 0 (canonical q).2 p := by
  refine Prod.ext ?_ ?_
  · funext i
    exact (sub_zero _).symm
  · exact ((sameRV_iff _ _).mp ((canonical_sameRV_iff p q).mpr h)).2

theorem canonical_open_images (A : DefSet (M := M) S 1 m) :
    CellwiseOpenMap (SpecialBijection.canonical A).toMap := by
  intro E hE hEA hcell
  obtain ⟨a, ha⟩ := hcell
  have he : unaryImage (SpecialBijection.canonical A).toMap E =
      unaryReframe 0 (canonical a.val).2 '' E := by
    ext q
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.val, hb, (canonical_eq_reframe (ha b.val hb)).symm⟩
    · rintro ⟨p, hp, hq⟩
      exact ⟨⟨p, hEA hp⟩, hp, (canonical_eq_reframe (ha p hp)).trans hq⟩
  rw [he]
  exact unaryReframe_open_polydisc _ _ hE

theorem inverse_keycell_image (T : SpecialBijection A B) (g : A → C) (a : B) :
    rvCellImage (g ∘ T.inverseMap) a = unaryImage g (T.inverseFibre a) := by
  ext q
  constructor
  · rintro ⟨b, hb, hq⟩
    refine ⟨T.inverseMap b, ⟨T.inverseMap b, rfl, ?_⟩, hq⟩
    simpa only [T.apply_inverse] using hb
  · rintro ⟨b, ⟨c, he, hc⟩, hq⟩
    have hcb : c = b := Subtype.ext he
    subst c
    refine ⟨T.toMap b, hc, ?_⟩
    simpa only [Function.comp_apply, T.inverse_apply] using hq

end IntegrationInACVF.Section5
