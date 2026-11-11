import IntegrationSection4.CellRectangles

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

namespace IntegrationInACVF.Section4.BalancedBallClasses

open Cells BalancedFibres GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def classes (D : Set (VF (M := M))) (γ : Values.Gamma (M := M)) : Set (Set M) :=
  {B | ∃ a ∈ D, B = gammaBall a γ true}

/-- An open ball containing two points at distance gamma contains the
entire gamma-ball around either point. -/
theorem ball_subset {D : Set (VF (M := M))} (hD : PaperBalls.IsOpenBall (rawSet D))
    (a x : VF (M := M)) (ha : a ∈ D) (hx : x ∈ D) (γ : Values.Gamma (M := M))
    (hValue : Values.vfValueHom (x-a) = γ.val) : gammaBall a γ true ⊆ rawSet D := by
  rcases hD with hWhole | ⟨c,β,hD⟩
  · intro z hz
    exact hWhole.symm ▸ hz.1
  · have ha' : a.val ∈ gammaBall c β true := hD ▸ (show a.val ∈ rawSet D from ⟨a,ha,rfl⟩)
    have hx' : x.val ∈ gammaBall c β true := hD ▸ (show x.val ∈ rawSet D from ⟨x,hx,rfl⟩)
    have hβ := GammaDifferenceRealization.difference_gt_radius c β a x ha' hx'
    rw [hValue] at hβ
    intro z hz
    let Z : VF (M := M) := ⟨z,hz.1⟩
    have hγ := GammaDifferenceRealization.difference_gt_radius a γ a Z
      (BallEnlargementGeometry.gammaBall_centre_mem a γ true) hz
    have hm := TranslatedRVGeometry.mem_of_value_gt a Z β (hβ.trans hγ)
    exact hD.symm ▸ (RadiusPreparationGeometry.recentre c a β ha' ▸ hm)

theorem source_subset {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D)) (ht : t₁ ≠ rv (0 : VF (M := M)))
    (a : VF (M := M)) (ha : a ∈ D) :
    gammaBall a ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht⟩ true ⊆ rawSet D := by
  obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t₁
  let x : VF (M := M) := a-u
  have he : a-x = u := by dsimp [x]; ring
  have hx : rv (a-x) = t₁ := by rw [he]; exact Subtype.ext (congrArg Subtype.val hu)
  have hxD := ((Set.ext_iff.mp (h.horizontal a ha) x).mpr hx).1
  apply ball_subset hD a x ha hxD
  rw [BalancedSlope.value_sub_swap x a]
  exact congrArg Values.vrv hx

theorem target_subset {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hE : PaperBalls.IsOpenBall (rawSet E)) (ht : t₂ ≠ rv (0 : VF (M := M)))
    (a : VF (M := M)) (ha : a ∈ D) :
    gammaBall (f a) ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht⟩ true ⊆ rawSet E := by
  obtain ⟨y,hy⟩ := translatedRV_nonempty t₂ (f a)
  have hp : (a,y) ∈ R := (Set.ext_iff.mp (h.vertical a ha) y).mpr hy
  exact ball_subset hE (f a) y (h.bijective.mapsTo ha) (h.subset hp).2 _ (congrArg Values.vrv hy)

theorem image_ball {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D))
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s)
    (a : VF (M := M)) (ha : a ∈ D) :
    rawMap f '' gammaBall a ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩ true =
      gammaBall (f a) ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩ true := by
  let γ₁ : Values.Gamma (M := M) := ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩
  let γ₂ : Values.Gamma (M := M) := ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩
  have hSub := source_subset h hD ht₁ a ha
  have hSlope := BalancedSlope.remark_4_6 h ht₁ a ha s hLin
  have hγ : s*γ₁ = γ₂ := by
    apply Subtype.ext
    rw [Values.gamma_val_mul,hSlope]
    exact div_mul_cancel₀ _ (fun he => γ₁.property (he.trans Values.infinity_eq_zero.symm))
  have him := LinearBallRadius.image_ball a γ₁ s (rawMap f)
    (fun z hz => rawMap_vf f D z (hSub hz))
    (GammaLinearRestrictions.mono hSub (rawMap f) (rawMap_vf f D) s hLin)
    ((hOO _ hSub).mp (Or.inr ⟨a,γ₁,rfl⟩))
  have hfa : (⟨rawMap f a.val,rawMap_vf f D a.val
      (hSub (BallEnlargementGeometry.gammaBall_centre_mem a γ₁ true))⟩ : VFType (M := M)) = f a :=
    Subtype.ext (rawMap_on f a)
  simpa only [hfa,hγ] using him

/-- The ball correspondence in the observation after Definition 4.5 is
an actual bijection of sets of balls, with no selected quotient codes. -/
theorem correspondence {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D))
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s) :
    Set.BijOn (fun B => rawMap f '' B)
      (classes D ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩)
      (classes E ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩) := by
  have him := image_ball h hD ht₁ ht₂ hOO s hLin
  have hinj : Set.InjOn (rawMap f) (rawSet D) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he
    rw [rawMap_on,rawMap_on] at he
    exact congrArg Subtype.val (h.bijective.injOn hx hy (Subtype.ext he))
  refine ⟨?_,?_,?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact ⟨f a,h.bijective.mapsTo ha,(him a ha)⟩
  · rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ he
    exact RadiusPreparationGeometry.image_injective (rawMap f) hinj
      (source_subset h hD ht₁ a ha) (source_subset h hD ht₁ b hb) he
  · rintro _ ⟨b,hb,rfl⟩
    obtain ⟨a,ha,rfl⟩ := h.bijective.surjOn hb
    exact ⟨_,⟨a,ha,rfl⟩,him a ha⟩

theorem fibres_constant {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D))
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s)
    (a x : VF (M := M)) (ha : a ∈ D)
    (hx : x.val ∈ gammaBall a ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩ true) :
    x ∈ D ∧ fibre R x = fibre R a := by
  have hxD := source_subset h hD ht₁ a ha hx
  obtain ⟨y,hy,he⟩ := hxD
  have hxD' : x ∈ D := (Subtype.ext he : y=x) ▸ hy
  have hfx : (f x).val ∈ gammaBall (f a)
      ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩ true := by
    rw [← image_ball h hD ht₁ ht₂ hOO s hLin a ha]
    exact ⟨x.val,hx,rawMap_on f x⟩
  exact ⟨hxD',(h.vertical x hxD').trans
    ((RVClassGeometry.centres_close t₂ ht₂ (f a) (f x) hfx).trans (h.vertical a ha).symm)⟩

/-- Balanced cells are the union of the corresponding source-ball and
vertical-fibre rectangles. This description depends only on the internal
balls and their correspondence. -/
theorem rectangle_union {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D))
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s) :
    R = {p | ∃ a ∈ D,
      p.1.val ∈ gammaBall a ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩ true ∧
      p.2 ∈ translatedRV t₂ (f a)} := by
  ext p
  constructor
  · intro hp
    have ha := (h.subset hp).1
    exact ⟨p.1,ha,BallEnlargementGeometry.gammaBall_centre_mem _ _ true,
      (Set.ext_iff.mp (h.vertical p.1 ha) p.2).mp hp⟩
  · rintro ⟨a,ha,hx,hy⟩
    obtain ⟨hxD,hFib⟩ := fibres_constant h hD ht₁ ht₂ hOO s hLin a p.1 ha hx
    change p.2 ∈ fibre R p.1
    rw [hFib,h.vertical a ha]
    exact hy



/-- The paradigm's ordinary radius is strictly inside either projection,
including a projection equal to the whole VF sort. -/
theorem projection_radius_lt (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {D : Set (VF (M := M))} (hD : PaperBalls.IsOpenBall (rawSet D))
    (a x : VF (M := M)) (ha : a ∈ D) (hx : x ∈ D) (γ : Values.Gamma (M := M))
    (hValue : Values.vfValueHom (x-a) = γ.val)
    (r : PaperBalls.Radius (M := M)) (hr : PaperBalls.HasRadius (rawSet D) r) :
    r < (↑γ.val : PaperBalls.Radius (M := M)) := by
  rcases hD with hWhole | ⟨c,β,hD⟩
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inl ⟨hWhole,rfl⟩)
    rw [he]
    exact WithBot.bot_lt_coe _
  · have he := PaperBallInvariants.hasRadius_unique δ hδ hr
      (Or.inr (Or.inr ⟨c,β,true,hD,rfl⟩))
    rw [he]
    apply WithBot.coe_lt_coe.mpr
    have ha' : a.val ∈ gammaBall c β true := hD ▸ (show a.val ∈ rawSet D from ⟨a,ha,rfl⟩)
    have hx' : x.val ∈ gammaBall c β true := hD ▸ (show x.val ∈ rawSet D from ⟨x,hx,rfl⟩)
    have hh := GammaDifferenceRealization.difference_gt_radius c β a x ha' hx'
    rwa [hValue] at hh

theorem positive_class_subset {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D)) (a : VF (M := M)) (ha : a ∈ D) :
    translatedRV t₁ a ⊆ D := by
  obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t₁
  let x : VF (M := M) := a-u
  have he : a-x = u := by dsimp [x]; ring
  have hx : rv (a-x) = t₁ := by rw [he]; exact Subtype.ext (congrArg Subtype.val hu)
  have hxD := ((Set.ext_iff.mp (h.horizontal a ha) x).mpr hx).1
  intro y hy
  have hValue : Values.vfValueHom (y-a) = Values.vfValueHom (x-a) := by
    rw [BalancedSlope.value_sub_swap x a]
    exact congrArg Values.vrv ((show rv (y-a) = t₁ from hy).trans hx.symm)
  have hm := RVInputFibre.translate_mem_of_value hD a x (y-a)
    (show a.val ∈ rawSet D from ⟨a,ha,rfl⟩) (show x.val ∈ rawSet D from ⟨x,hxD,rfl⟩) hValue
  have hs : a+(y-a) = y := by ring
  rw [hs] at hm
  obtain ⟨z,hz,he⟩ := hm
  exact (Subtype.ext he : z=y) ▸ hz

/-- The second rectangle description of the internal symmetry after 4.5.
The first factor is the translate of the inverse ball by the first RV
paradigm, and the second factor is the corresponding target ball. -/
theorem symmetric_rectangle_union {D E : Set (VF (M := M))}
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : HasBalancedFibres D E R f t₁ t₂)
    (hD : PaperBalls.IsOpenBall (rawSet D))
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s) :
    R = {p | ∃ a ∈ D, p.1 ∈ translatedRV t₁ a ∧
      p.2.val ∈ gammaBall (f a) ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩ true} := by
  ext p
  constructor
  · intro hp
    have hpD := (h.subset hp).1
    obtain ⟨a,ha,he⟩ := h.bijective.surjOn (h.subset hp).2
    have hp' : a ∈ D ∩ f ⁻¹' fibre R p.1 := by
      refine ⟨ha,?_⟩
      change f a ∈ fibre R p.1
      rw [he]
      exact hp
    have hx := (Set.ext_iff.mp (h.horizontal p.1 hpD) a).mp hp'
    exact ⟨a,ha,hx,he.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem p.2 _ true⟩
  · rintro ⟨a,ha,hx,hy⟩
    have hpD := positive_class_subset h hD a ha hx
    have hy' := (image_ball h hD ht₁ ht₂ hOO s hLin a ha).symm ▸ hy
    obtain ⟨z,hz,hfz⟩ := hy'
    let Z : VF (M := M) := ⟨z,hz.1⟩
    have hzD := source_subset h hD ht₁ a ha hz
    obtain ⟨w,hw,he⟩ := hzD
    have hZD : Z ∈ D := (Subtype.ext he : w=Z) ▸ hw
    have hRV : p.1 ∈ translatedRV t₁ Z :=
      (RVClassGeometry.centres_close t₁ ht₁ a Z hz).symm ▸ hx
    have hh := (Set.ext_iff.mp (h.horizontal p.1 hpD) Z).mpr hRV
    have hOut : f Z = p.2 := Subtype.ext ((rawMap_on f Z).symm.trans hfz)
    change p.2 ∈ fibre R p.1
    rw [← hOut]
    exact hh.2

end IntegrationInACVF.Section4.BalancedBallClasses
