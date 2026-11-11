import IntegrationSection4.BalancedCompletion

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.CellsFromFibres

open BalancedFibres Cells

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def relation (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M)) :
    Set (VF (M := M) × VF (M := M)) := {p | p.1 ∈ D ∧ p.2 ∈ translatedRV t (f p.1)}

theorem first_eq (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M)) :
    first (relation D f t) = D := by
  ext a
  constructor
  · rintro ⟨p,hp,rfl⟩
    exact hp.1
  · intro ha
    obtain ⟨b,hb⟩ := translatedRV_nonempty t (f a)
    exact ⟨(a,b),⟨ha,hb⟩,rfl⟩

theorem fibre_eq (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (a : VF (M := M)) (ha : a ∈ D) : fibre (relation D f t) a = translatedRV t (f a) := by
  ext b
  exact ⟨fun h => h.2,fun h => ⟨ha,h⟩⟩

theorem constant (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hCell : IsOneCell D)
    (hPoly : ∃ u v : RV (M := M), ∀ p ∈ relation D f t, rv p.1 = u ∧ rv p.2 = v)
    (hConst : ∀ a ∈ D, ∀ b ∈ D, f a = f b) : CellData (relation D f t) f t := by
  refine ⟨hPoly,?_,?_,?_⟩
  · rwa [first_eq]
  · intro a ha
    exact fibre_eq D f t a ((first_eq D f t) ▸ ha)
  · left
    rwa [first_eq]

theorem separated (D : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t : RV (M := M))
    (hCell : IsOneCell D)
    (hPoly : ∃ u v : RV (M := M), ∀ p ∈ relation D f t, rv p.1 = u ∧ rv p.2 = v)
    (hInj : Set.InjOn f D) (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (r : PaperBalls.Radius (M := M)) (hr : PaperBalls.HasRadius (rawSet (f '' D)) r)
    (htr : (↑(Values.vrv t) : PaperBalls.Radius (M := M)) ≤ r) : CellData (relation D f t) f t := by
  refine ⟨hPoly,?_,?_,?_⟩
  · rwa [first_eq]
  · intro a ha
    exact fibre_eq D f t a ((first_eq D f t) ▸ ha)
  · right; left
    rw [first_eq]
    exact ⟨hInj,hOO,r,hr,htr⟩

/-- Assemble the balanced alternative from actual translated vertical
fibres, coverage of the positioning image, and the checked horizontal
completion. The source and target here are actual projection sets. -/
theorem balanced (D E : Set (VF (M := M))) (f : VF (M := M) → VF (M := M)) (t₁ t₂ : RV (M := M))
    (hCell : IsOneCell D)
    (hPoly : ∃ u v : RV (M := M), ∀ p ∈ relation D f t₂, rv p.1 = u ∧ rv p.2 = v)
    (hbij : Set.BijOn f D E)
    (hSub : ∀ a ∈ D, translatedRV t₂ (f a) ⊆ E)
    (hCover : ∀ b ∈ E, ∃ a ∈ D, b ∈ translatedRV t₂ (f a))
    (hD : PaperBalls.IsOpenBall (rawSet D)) (hE : PaperBalls.IsOpenBall (rawSet E))
    (hOO : MaximalOpenClasses.OpenToOpen (rawSet D) (rawMap f))
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (rawSet D) (rawMap f) (rawMap_vf f D) s)
    (hConst : ∀ a ∈ D, ∀ x ∈ D, f x ∈ translatedRV t₂ (f a) → rv (a-x) = t₁) :
    CellData (relation D f t₂) f t₂ := by
  have hRSub : relation D f t₂ ⊆ D ×ˢ E := fun p hp => ⟨hp.1,hSub _ hp.1 hp.2⟩
  have hSecond : second (relation D f t₂) = E := by
    ext b
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact (hRSub hp).2
    · intro hb
      obtain ⟨a,ha,hab⟩ := hCover b hb
      exact ⟨(a,b),⟨ha,hab⟩,rfl⟩
  have hBal := BalancedCompletion.of_constant_difference D E (relation D f t₂) f t₁ t₂
    hbij hRSub (fibre_eq D f t₂) hD hOO s hLin
    (fun a ha x hx h => hConst a ha x hx ((fibre_eq D f t₂ a ha) ▸ h))
  refine ⟨hPoly,?_,?_,?_⟩
  · rwa [first_eq]
  · intro a ha
    exact fibre_eq D f t₂ a ((first_eq D f t₂) ▸ ha)
  · right; right
    refine ⟨t₁,?_⟩
    change PaperBalls.IsOpenBall (rawSet (first (relation D f t₂))) ∧
      PaperBalls.IsOpenBall (rawSet (second (relation D f t₂))) ∧
      HasBalancedFibres (first (relation D f t₂)) (second (relation D f t₂)) (relation D f t₂) f t₁ t₂ ∧
      MaximalOpenClasses.OpenToOpen (rawSet (first (relation D f t₂))) (rawMap f) ∧
      ∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (rawSet (first (relation D f t₂)))
        (rawMap f) (rawMap_vf f (first (relation D f t₂))) s
    rw [first_eq,hSecond]
    exact ⟨hD,hE,hBal,hOO,s,hLin⟩

end IntegrationInACVF.Section4.CellsFromFibres
