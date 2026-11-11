import IntegrationSection4.LinearRVClasses

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.BalancedCompletion

open BalancedFibres Cells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem raw_injective {D : Set (VF (M := M))} (f : VF (M := M) → VF (M := M))
    (hInj : Set.InjOn f D) : Set.InjOn (rawMap f) (rawSet D) := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
  rw [rawMap_on,rawMap_on] at he
  exact congrArg Subtype.val (hInj hx hy (Subtype.ext he))

/-- The singleton inverse-difference conclusion of 4.4, together with
Gamma-linearity and open-to-open, gives the full horizontal fibre identity
in 4.5. No reverse containment is assumed. -/
theorem of_constant_difference (D E : Set (VF (M := M)))
    (R : Set (VF (M := M) × VF (M := M))) (f : VF (M := M) → VF (M := M))
    (t₁ t₂ : RV (M := M)) (hbij : Set.BijOn f D E) (hSub : R ⊆ D ×ˢ E)
    (hVertical : ∀ a ∈ D, fibre R a = translatedRV t₂ (f a))
    (hOpen : PaperBalls.IsOpenBall (rawSet D))
    (hoo : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s)
    (hConst : ∀ a ∈ D, ∀ x ∈ D, f x ∈ fibre R a → rv (a-x) = t₁) :
    HasBalancedFibres D E R f t₁ t₂ := by
  refine ⟨hbij,hSub,hVertical,?_⟩
  intro a ha
  obtain ⟨b,hb⟩ := translatedRV_nonempty t₂ (f a)
  have hbR : b ∈ fibre R a := (hVertical a ha).symm ▸ hb
  obtain ⟨x,hx,hfx⟩ := hbij.2.2 (hSub hbR).2
  have hxR : f x ∈ fibre R a := hfx.symm ▸ hbR
  have ht₁ := hConst a ha x hx hxR
  ext z
  constructor
  · rintro ⟨hz,hfz⟩
    exact hConst a ha z hz hfz
  · intro hz
    change rv (a-z) = t₁ at hz
    by_cases hxa : x = a
    · subst x
      have ht0 : t₁ = rv (0 : VF (M := M)) := by simpa only [sub_self] using ht₁.symm
      have hza : z = a := by
        rw [ht0,rv_eq_zero_iff,sub_eq_zero] at hz
        exact hz.symm
      subst z
      exact ⟨ha,hxR⟩
    · have hh := InverseDifferenceGeometry.reverse_difference (0 : VF (M := M)) (a-z) (a-x)
        (by simpa only [sub_zero,rv] using congrArg Subtype.val (hz.trans ht₁.symm))
      have hClass : rv (z-a) = rv (x-a) := Subtype.ext (by simpa only [zero_sub,neg_sub,rv] using hh)
      have hzClass : z ∈ translatedRV (rv (x-a)) a := hClass
      have hzD : z ∈ D := by
        have hh := TranslatedRVGeometry.subset_open hOpen (rv (x-a)) a x
          ⟨a,ha,rfl⟩ ⟨x,hx,rfl⟩ (show x ∈ translatedRV (rv (x-a)) a from rfl)
        obtain ⟨u,hu,he⟩ := hh ⟨z,hzClass,rfl⟩
        exact (Subtype.ext he : u = z) ▸ hu
      have hImage := LinearRVClasses.image_class (rawSet D) hOpen (rawMap f) (rawMap_vf f D)
        (raw_injective f hbij.2.1) hoo s hLin a x (f a) (f x)
        ⟨a,ha,rfl⟩ ⟨x,hx,rfl⟩ hxa (rawMap_on f a) (rawMap_on f x)
      have hOut : (f z).val ∈ rawSet (translatedRV (rv (f x-f a)) (f a)) := by
        rw [← hImage,← rawMap_on f z]
        exact ⟨z.val,⟨z,hzClass,rfl⟩,rfl⟩
      obtain ⟨v,hv,hvz⟩ := hOut
      have hvz' : v = f z := Subtype.ext hvz
      have hParadigm : rv (f x-f a) = t₂ := by
        have hh : f x ∈ translatedRV t₂ (f a) := by rw [← hVertical a ha]; exact hxR
        exact hh
      refine ⟨hzD,?_⟩
      rw [hVertical a ha]
      change rv (f z-f a) = t₂
      rw [hvz'] at hv
      have hv' : rv (f z-f a) = rv (f x-f a) := hv
      exact hv'.trans hParadigm

end IntegrationInACVF.Section4.BalancedCompletion
