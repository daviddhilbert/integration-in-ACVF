module

public import Integration7.PreparedBallRectangleGeometry
public import IntegrationSection4.TranslatedRVGeometry

@[expose] public section

/-! Restricting a balanced relation to a matching positioning ball
retains its complete vertical and horizontal RV fibres whenever that
ball meets the relation. The source ball need not be atomic. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

private theorem mem_raw_set {E : Set (VF (M := M))} (x : VF (M := M)) :
    x.val ∈ Cells.rawSet E ↔ x ∈ E := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (Subtype.ext he) ▸ hy
  · intro h
    exact ⟨x,h,rfl⟩

theorem translated_rv_classes_stay_in_open_ball {E : Set (VF (M := M))}
    (hE : PaperBalls.IsOpenBall (Cells.rawSet E))
    (t : RV (M := M)) (c₀ x₀ : VF (M := M)) (hc₀ : c₀ ∈ E) (hx₀ : x₀ ∈ E)
    (hTag : x₀ ∈ BalancedFibres.translatedRV t c₀) :
    ∀ c ∈ E, BalancedFibres.translatedRV t c ⊆ E := by
  rcases hE with hVF | ⟨d,β,hBall⟩
  · intro c hc z hz
    apply (mem_raw_set z).mp
    exact hVF.symm ▸ z.property
  · have hcBall := hBall ▸ (mem_raw_set c₀).mpr hc₀
    have hxBall := hBall ▸ (mem_raw_set x₀).mpr hx₀
    have hRadius := GammaDifferenceRealization.difference_gt_radius d β c₀ x₀ hcBall hxBall
    have hValue := congrArg Values.vrv (show rv (x₀-c₀) = t from hTag)
    have hβt : β.val < Values.vrv t := hValue ▸ hRadius
    intro c hc z hz
    apply (mem_raw_set z).mp
    apply Eq.mp (congrArg (fun X : Set M => z.val ∈ X) hBall.symm)
    exact (TranslatedRVGeometry.cover_ordinary d β t hβt).1 c
      (hBall ▸ (mem_raw_set c).mpr hc) ⟨z,hz,rfl⟩

theorem balanced_fibres_restrict_matching_open_ball
    {D E B C : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (hR : BalancedFibres.HasBalancedFibres D E R f r t)
    (hBD : B ⊆ D) (hImage : f '' B = C) (hC : PaperBalls.IsOpenBall (Cells.rawSet C))
    (hNonempty : (R ∩ (B ×ˢ C)).Nonempty) :
    BalancedFibres.HasBalancedFibres B C (R ∩ (B ×ˢ C)) f r t := by
  obtain ⟨p,hpR,hpB,hpC⟩ := hNonempty
  have hfpC : f p.1 ∈ C := hImage ▸ ⟨p.1,hpB,rfl⟩
  have hTag : p.2 ∈ BalancedFibres.translatedRV t (f p.1) :=
    (Set.ext_iff.mp (hR.vertical p.1 (hBD hpB)) p.2).mp hpR
  have hClasses := translated_rv_classes_stay_in_open_ball hC t (f p.1) p.2 hfpC hpC hTag
  have hClass (a : VF (M := M)) (ha : a ∈ B) :
      BalancedFibres.translatedRV t (f a) ⊆ C := hClasses (f a) (hImage ▸ ⟨a,ha,rfl⟩)
  refine ⟨?_,fun _ h => h.2,?_,?_⟩
  · refine ⟨fun a ha => hImage ▸ ⟨a,ha,rfl⟩,?_,?_⟩
    · intro x hx y hy he
      exact hR.bijective.2.1 (hBD hx) (hBD hy) he
    · intro c hc
      exact (Set.ext_iff.mp hImage c).mpr hc
  · intro a ha
    ext y
    constructor
    · intro h
      exact (Set.ext_iff.mp (hR.vertical a (hBD ha)) y).mp h.1
    · intro h
      exact ⟨(Set.ext_iff.mp (hR.vertical a (hBD ha)) y).mpr h,ha,hClass a ha h⟩
  · intro a ha
    ext x
    constructor
    · rintro ⟨hx,hax⟩
      exact (Set.ext_iff.mp (hR.horizontal a (hBD ha)) x).mp ⟨hBD hx,hax.1⟩
    · intro hx
      have hOld := (Set.ext_iff.mp (hR.horizontal a (hBD ha)) x).mpr hx
      have hfC : f x ∈ C := hClass a ha
        ((Set.ext_iff.mp (hR.vertical a (hBD ha)) (f x)).mp hOld.2)
      obtain ⟨b,hb,hbx⟩ := (Set.ext_iff.mp hImage (f x)).mpr hfC
      have he : b = x := hR.bijective.2.1 (hBD hb) hOld.1 hbx
      exact ⟨he ▸ hb,hOld.2,ha,hfC⟩

theorem balanced_fibres_restrict_matching_one_cells
    {D E B C : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {r t : RV (M := M)} (hR : BalancedFibres.HasBalancedFibres D E R f r t)
    (hBD : B ⊆ D) (hImage : f '' B = C)
    (hB : Cells.IsOneCell B) (hC : Cells.IsOneCell C)
    (ht : t ≠ rv (0 : VF (M := M))) (hNonempty : (R ∩ (B ×ˢ C)).Nonempty) :
    PaperBalls.IsOpenBall (Cells.rawSet B) ∧ PaperBalls.IsOpenBall (Cells.rawSet C) ∧
      BalancedFibres.HasBalancedFibres B C (R ∩ (B ×ˢ C)) f r t := by
  obtain ⟨p,hpR,hpB,hpC⟩ := hNonempty
  have hOpenC : PaperBalls.IsOpenBall (Cells.rawSet C) := by
    rcases hC with ⟨c,hc⟩ | ⟨ho,_⟩
    · have hfpC : f p.1 ∈ C := hImage ▸ ⟨p.1,hpB,rfl⟩
      have he : p.2 = f p.1 := (hc ▸ hpC).trans (hc ▸ hfpC).symm
      have hTag := (Set.ext_iff.mp (hR.vertical p.1 (hBD hpB)) p.2).mp hpR
      change rv (p.2-f p.1) = t at hTag
      rw [he,sub_self] at hTag
      exact (ht hTag.symm).elim
    · exact ho
  have hNew := balanced_fibres_restrict_matching_open_ball hR hBD hImage hOpenC
    ⟨p,hpR,hpB,hpC⟩
  have hr : r ≠ rv (0 : VF (M := M)) := fun h => ht
    ((BalancedFibres.paradigms_degenerate_together hNew p.1 hpB).mp h)
  have hOpenB : PaperBalls.IsOpenBall (Cells.rawSet B) := by
    rcases hB with ⟨c,hc⟩ | ⟨ho,_⟩
    · obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective r
      let x := p.1-u
      have hTag : rv (p.1-x) = r := by
        have he : p.1-x = u := by dsimp [x]; ring
        rw [he]
        exact Subtype.ext (congrArg Subtype.val hu)
      have hxB := ((Set.ext_iff.mp (hNew.horizontal p.1 hpB) x).mpr hTag).1
      have he : p.1 = x := (hc ▸ hpB).trans (hc ▸ hxB).symm
      rw [← he,sub_self] at hTag
      exact (hr hTag.symm).elim
    · exact ho
  exact ⟨hOpenB,hOpenC,hNew⟩

end IntegrationInACVF.Section7
