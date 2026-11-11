import IntegrationSection4.RadiusRelationSyntax
import IntegrationSection4.RadiusPreparationGeometry
import IntegrationSection4.InverseBodies

/-! Corrected Lemma 4.3: the set of source radii has at most one element.
The preparation works simultaneously for every ordinary target radius. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
open GammaRadiusAtomicity IntegrationInACVF.Section4.RadiusPreparationGeometry

namespace IntegrationInACVF.Section4.RadiusPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def radiusSet (f : M → M) (E : Set M) (α : Values.Gamma (M := M)) :
    Set (PaperBalls.Radius (M := M)) :=
  {r | ∃ D : Set M, PaperBalls.IsOpenBall D ∧ D ⊆ E ∧ PaperBalls.HasRadius D r ∧
    PaperBalls.HasRadius (f '' D) (↑α.val : PaperBalls.Radius (M := M))}

theorem compare_whole (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M) (hf : Set.InjOn f A)
    (hoo : MaximalOpenClasses.OpenToOpen A f)
    (α : Values.Gamma (M := M)) {D E : Set M}
    (hD : PaperBalls.IsOpenBall D) (hE : PaperBalls.IsOpenBall E)
    (hDA : D ⊆ A) (hEA : E ⊆ A) (hDVF : D = {x | iVF x})
    (hDr : PaperBalls.HasRadius (f '' D) (↑α.val : PaperBalls.Radius (M := M)))
    (hEr : PaperBalls.HasRadius (f '' E) (↑α.val : PaperBalls.Radius (M := M))) : D = E := by
  obtain ⟨x,hx⟩ := open_nonempty hE
  have hxD : x ∈ D := hDVF.symm ▸ hAVF (hEA hx)
  exact image_injective f hf hDA hEA
    (equal_of_meet δ hδ ((hoo D hDA).mp hD) ((hoo E hEA).mp hE) α hDr hEr
      (f x) ⟨x,hxD,rfl⟩ ⟨x,hx,rfl⟩)

theorem rows_on_body {S : Set M} {l : ℕ} {D : DefSet (M := M) S 1 0}
    {E : DefSet (M := M) S 1 l} (A : Set M) (f : M → M) (T : SpecialBijection D E)
    (hUniform : FiniteRelationPreparation.Uniform (RadiusRelationSyntax.relation A f) T)
    (b : E) (x y : VF (M := M)) (hx : x.val ∈ InverseBodies.body T b)
    (hy : y.val ∈ InverseBodies.body T b) (β α : Values.Gamma (M := M)) :
    (gammaBall x β true ⊆ A ∧ ∃ d : VFType (M := M), f '' gammaBall x β true = gammaBall d α true) ↔
    (gammaBall y β true ⊆ A ∧ ∃ d : VFType (M := M), f '' gammaBall y β true = gammaBall d α true) := by
  obtain ⟨r,hr,hrβ⟩ := EndpointLogic.codeValue_surjective β
  obtain ⟨s,hs,hsα⟩ := EndpointLogic.codeValue_surjective α
  obtain ⟨a,ha,haKey⟩ := hx
  obtain ⟨c,hc,hcKey⟩ := hy
  let q : Point (M := M) 0 2 := (Fin.elim0,![⟨r,hr.1⟩,⟨s,hs.1⟩])
  have hh := hUniform (T.toMap a) (T.toMap c) (haKey.trans hcKey.symm) q
  rw [T.inverse_apply,T.inverse_apply] at hh
  change (NonzeroRV r ∧ NonzeroRV s ∧ RadiusRelationSyntax.row A f ![r,s,(vfAt a.val 0).val]) ↔
    (NonzeroRV r ∧ NonzeroRV s ∧ RadiusRelationSyntax.row A f ![r,s,(vfAt c.val 0).val]) at hh
  have hax : vfAt a.val 0 = x := Subtype.ext ha
  have hcy : vfAt c.val 0 = y := Subtype.ext hc
  rw [hax,hcy] at hh
  have hRow : RadiusRelationSyntax.row A f ![r,s,x.val] ↔ RadiusRelationSyntax.row A f ![r,s,y.val] :=
    ⟨fun h => (hh.mp ⟨hr,hs,h⟩).2.2,fun h => (hh.mpr ⟨hr,hs,h⟩).2.2⟩
  rw [RadiusRelationSyntax.row_iff A f r s hr hs x,
    RadiusRelationSyntax.row_iff A f r s hr hs y,hrβ,hsα] at hRow
  exact hRow

theorem subsingleton_on_body {S : Set M} {l : ℕ} {D : DefSet (M := M) S 1 0}
    {E : DefSet (M := M) S 1 l} (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : Set M) (hAVF : A ⊆ {x | iVF x}) (f : M → M) (hf : Set.InjOn f A)
    (hoo : MaximalOpenClasses.OpenToOpen A f) (T : SpecialBijection D E)
    (hUniform : FiniteRelationPreparation.Uniform (RadiusRelationSyntax.relation A f) T)
    (b : E) (hBA : InverseBodies.body T b ⊆ A) (α : Values.Gamma (M := M)) :
    (radiusSet f (InverseBodies.body T b) α).Subsingleton := by
  rintro r ⟨U,hU,hUB,hr,hUr⟩ s ⟨V,hV,hVB,hs,hVr⟩
  have hUA : U ⊆ A := hUB.trans hBA
  have hVA : V ⊆ A := hVB.trans hBA
  rcases hU with hUVF | ⟨c,β,hU⟩
  · have he := compare_whole δ hδ A hAVF f hf hoo α (Or.inl hUVF) hV hUA hVA hUVF hUr hVr
    exact PaperBallInvariants.hasRadius_unique δ hδ hr (he.symm ▸ hs)
  rcases hV with hVVF | ⟨d,γ,hV⟩
  · have he := compare_whole δ hδ A hAVF f hf hoo α (Or.inl hVVF) (Or.inr ⟨c,β,hU⟩)
      hVA hUA hVVF hVr hUr
    exact PaperBallInvariants.hasRadius_unique δ hδ hr (he ▸ hs)
  have hc : c.val ∈ U := hU.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem c β true
  have hd : d.val ∈ V := hV.symm ▸ BallEnlargementGeometry.gammaBall_centre_mem d γ true
  obtain ⟨e,he⟩ := AffineHoleGeometry.open_ordinary_presentation δ hδ
    ((hoo V hVA).mp (Or.inr ⟨d,γ,hV⟩)) α hVr
  have hAtD : gammaBall d γ true ⊆ A ∧ ∃ e : VFType (M := M),
      f '' gammaBall d γ true = gammaBall e α true := ⟨hV ▸ hVA,e,hV ▸ he⟩
  obtain ⟨hCA,e',he'⟩ := (rows_on_body A f T hUniform b c d (hUB hc) (hVB hd) γ α).mpr hAtD
  let C := gammaBall c γ true
  have hCo : PaperBalls.IsOpenBall C := Or.inr ⟨c,γ,rfl⟩
  have hCr : PaperBalls.HasRadius (f '' C) (↑α.val : PaperBalls.Radius (M := M)) :=
    Or.inr (Or.inr ⟨e',α,true,he',rfl⟩)
  have hcC : c.val ∈ C := BallEnlargementGeometry.gammaBall_centre_mem c γ true
  have hImages := equal_of_meet δ hδ ((hoo U hUA).mp (Or.inr ⟨c,β,hU⟩))
    ((hoo C hCA).mp hCo) α hUr hCr (f c.val) ⟨c.val,hc,rfl⟩ ⟨c.val,hcC,rfl⟩
  have hUC := image_injective f hf hUA hCA hImages
  have hrγ : r = (↑γ.val : PaperBalls.Radius (M := M)) :=
    PaperBallInvariants.hasRadius_unique δ hδ hr (Or.inr (Or.inr ⟨c,γ,true,hUC,rfl⟩))
  have hsγ : s = (↑γ.val : PaperBalls.Radius (M := M)) :=
    PaperBallInvariants.hasRadius_unique δ hδ hs (Or.inr (Or.inr ⟨d,γ,true,hV,rfl⟩))
  exact hrγ.trans hsγ.symm

/-- Lemma 4.3, with the author-approved “has at most one element” correction.
One preparation works for all ordinary target radii, including unnamed ones. -/
theorem lemma_4_3 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) (δ : Values.Gamma (M := M)) (hδ : 1 < δ)
    (A : Set M) (hA : DefinableAtBase G .vf A) (f : M → M)
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (ImaginaryBaseImages.graphOn A f))
    (hInj : Set.InjOn f A) (hoo : MaximalOpenClasses.OpenToOpen A f) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
      ∃ T : GammaSpecialBijection G (GammaUnarySyntax.pointSet A) E,
        IsRVPullback E ∧ ∀ b : T.target,
          (InverseBodies.body T.special b ⊆ A) ∧ ∀ α : Values.Gamma (M := M),
            (radiusSet f (InverseBodies.body T.special b) α).Subsingleton := by
  have hAF := GammaBaseBridge.of_gamma G hA
  have hfF := GammaBaseBridge.of_gamma G hf
  obtain ⟨l,E,T,hE,hR⟩ := UnaryPreparation.prepare hs h00 G hsmall hGenerated A hA
    (RadiusRelationSyntax.relation A f) (RadiusRelationSyntax.relation_definable G A f hAF hfF)
  refine ⟨l,E,T,hE,?_⟩
  intro b
  have hBA : InverseBodies.body T.special b ⊆ A := by
    rintro x ⟨a,ha,_⟩
    have hh := (Set.ext_iff.mp T.source_eq a.val).mp a.property
    change (vfAt a.val 0).val ∈ A at hh
    rwa [ha] at hh
  refine ⟨hBA,fun α => subsingleton_on_body δ hδ A hA.proper f hInj hoo T.special hR b hBA α⟩

end IntegrationInACVF.Section4.RadiusPreparation
