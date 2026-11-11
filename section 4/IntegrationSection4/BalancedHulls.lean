import IntegrationSection4.BalancedBallClasses

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.BalancedHulls

open Cells BalancedFibres GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The first three nondegenerate observations after Definition 4.5:
actual minimal closed hulls centred at the positioning values, the two
paradigm radii, their strict bounds inside the projection balls, and the
omitted positioning points. No definable choice of a hull code is assumed. -/
theorem observations {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    {R : Set (VF (M := M) × VF (M := M))} {f : VF (M := M) → VF (M := M)}
    {t₁ t₂ : RV (M := M)} (h : IsBalanced R f t₁ t₂)
    (ht₁ : t₁ ≠ rv (0 : VF (M := M))) (ht₂ : t₂ ≠ rv (0 : VF (M := M)))
    (a : VF (M := M)) (ha : a ∈ first R) :
    ∃ x ∈ first R, ∃ y ∈ fibre R a,
      Values.vfValueHom (x-a) = Values.vrv t₁ ∧
      Values.vfValueHom (y-f a) = Values.vrv t₂ ∧
      FiniteClosedHull.IsHull v (first R ∩ f ⁻¹' fibre R a) a (x-a) ∧
      FiniteClosedHull.IsHull v (fibre R a) (f a) (y-f a) ∧
      a ∉ first R ∩ f ⁻¹' fibre R a ∧ f a ∉ fibre R a ∧
      (∀ r₁ r₂ : PaperBalls.Radius (M := M),
        PaperBalls.HasRadius (rawSet (first R)) r₁ →
        PaperBalls.HasRadius (rawSet (second R)) r₂ →
        r₁ < ↑(Values.vrv t₁) ∧ r₂ < ↑(Values.vrv t₂)) := by
  rcases h with ⟨hD,hE,hFib,hOO,s,hLin⟩
  obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t₁
  let x : VF (M := M) := a-u
  have he : a-x = u := by dsimp [x]; ring
  have hx : rv (a-x) = t₁ := by rw [he]; exact Subtype.ext (congrArg Subtype.val hu)
  have hxD := ((Set.ext_iff.mp (hFib.horizontal a ha) x).mpr hx).1
  obtain ⟨y,hy⟩ := translatedRV_nonempty t₂ (f a)
  have hyR : y ∈ fibre R a := (Set.ext_iff.mp (hFib.vertical a ha) y).mpr hy
  have hyE := (hFib.subset hyR).2
  have hHx := RVClassGeometry.reverse_closed_hull v hv δ hδ t₁ ht₁ a x hx
  have hHy := RVClassGeometry.closed_hull v hv δ hδ t₂ ht₂ (f a) y hy
  refine ⟨x,hxD,y,hyR,hHx.1,hHy.1,?_,?_,?_,?_,?_⟩
  · rw [hFib.horizontal a ha]
    exact hHx.2
  · rw [hFib.vertical a ha]
    exact hHy.2
  · exact fun hh => positioning_not_in_fibre hFib ht₂ a ha hh.2
  · exact positioning_not_in_fibre hFib ht₂ a ha
  · intro r₁ r₂ hr₁ hr₂
    exact ⟨BalancedBallClasses.projection_radius_lt δ hδ hD a x ha hxD
      ⟨Values.vrv t₁,TranslatedRVGeometry.value_ne_infinity t₁ ht₁⟩ hHx.1 r₁ hr₁,
      BalancedBallClasses.projection_radius_lt δ hδ hE (f a) y (hFib.bijective.mapsTo ha) hyE
      ⟨Values.vrv t₂,TranslatedRVGeometry.value_ne_infinity t₂ ht₂⟩ hHy.1 r₂ hr₂⟩

end IntegrationInACVF.Section4.BalancedHulls
