import IntegrationSection4.InverseRowsOnBall
import IntegrationSection4.InverseOneCells
import IntegrationSection4.TranslatedFamilySyntax
import IntegrationSection4.CellsFromFibres
import IntegrationSection4.ScalarPositioning

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.PreparedBodyCells

open BalancedFibres Cells ScalarPositioning

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The geometric assembly for an injective positioning row. A prepared
inverse relation and the actual image radius give precisely alternatives
(b) and (c), with singleton source pieces covered by alternative (a). -/
theorem cell {S : Set M} {m l : ℕ}
    {U : DefSet (M := M) S 1 m} {V : DefSet (M := M) S 1 l}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hInj : ∀ p, Set.InjOn (f p) (A p)) (j : Fin m) (T : SpecialBijection U V)
    (hU : carrier U = GammaFamilySyntax.domain A) (hV : IsRVPullback (carrier V))
    (hUniform : FiniteRelationPreparation.Uniform
      (FamilyInverseDifferences.relation A f (TranslatedFamilySyntax.relation A f j)) T)
    (b : V) (φ : VF (M := M) → VF (M := M))
    (hφ : ∀ x ∈ InverseBodies.body T b,
      rawMap φ x = f (GammaFamilySyntax.labels (T.inverseMap b).val) x)
    (s : Values.Gamma (M := M))
    (hLin : GammaLinearity.GammaLinear (InverseBodies.body T b)
      (f (GammaFamilySyntax.labels (T.inverseMap b).val))
      (fun x hx => hfVF _ x (FamilyPreparedLinearity.body_subset A T hU b hx)) s)
    (hOO : MaximalOpenClasses.OpenToOpen (InverseBodies.body T b)
      (f (GammaFamilySyntax.labels (T.inverseMap b).val)))
    (hPoly : ∃ u v : RV (M := M), ∀ q ∈ CellsFromFibres.relation
      (vfSet (InverseBodies.body T b)) φ ((T.inverseMap b).val.2 j), rv q.1 = u ∧ rv q.2 = v) :
    CellData (CellsFromFibres.relation (vfSet (InverseBodies.body T b)) φ ((T.inverseMap b).val.2 j))
      φ ((T.inverseMap b).val.2 j) := by
  let p := GammaFamilySyntax.labels (T.inverseMap b).val
  let D := InverseBodies.body T b
  let Dv := vfSet D
  let t := (T.inverseMap b).val.2 j
  let R := TranslatedFamilySyntax.relation A f j
  have hDA : D ⊆ A p := FamilyPreparedLinearity.body_subset A T hU b
  have hDVF : D ⊆ {x | iVF x} := fun x hx => hAVF p (hDA hx)
  have hfD : ∀ x ∈ D, iVF (f p x) := fun x hx => hfVF p x (hDA hx)
  have hDInj : Set.InjOn (f p) D := fun x hx y hy he => hInj p (hDA hx) (hDA hy) he
  have hφval (x : VF (M := M)) (hx : x.val ∈ D) : (φ x).val = f p x.val :=
    (rawMap_on φ x).symm.trans (hφ x.val hx)
  have hRow (a y : VF (M := M)) (ha : a.val ∈ D) :
      ![a.val,y.val] ∈ R p ↔ y ∈ translatedRV t (φ a) := by
    change (a.val ∈ A p ∧ iVF y.val ∧ RVDifferencePairs.difference y.val (f p a.val) = t.val) ↔ _
    rw [← hφval a ha,RVDifferencePairs.difference_vf y (φ a)]
    simp only [hDA ha,y.property,true_and]
    change (iRv (y-φ a).val = t.val) ↔ rv (y-φ a) = t
    exact ⟨fun h => Subtype.ext (by simpa only [rv] using h),
      fun h => by simpa only [rv] using congrArg Subtype.val h⟩
  have hOne : IsOneCell Dv := InverseOneCells.one_cell T hV b
  rcases hOne with ⟨a,hDa⟩ | ⟨hDo,hDRV⟩
  · apply CellsFromFibres.constant Dv φ t (Or.inl ⟨a,hDa⟩) hPoly
    intro x hx y hy
    rw [hDa] at hx hy
    exact congrArg φ (hx.trans hy.symm)
  · have hOne : IsOneCell Dv := Or.inr ⟨hDo,hDRV⟩
    have hDOpen : PaperBalls.IsOpenBall D := (raw_vfSet D hDVF) ▸ hDo
    have hφVF : ∀ x ∈ D, iVF (rawMap φ x) := by
      intro x hx
      rw [hφ x hx]
      exact hfD x hx
    have hOOφ : MaximalOpenClasses.OpenToOpen (rawSet Dv) (rawMap φ) := by
      rw [raw_vfSet D hDVF]
      exact open_congr (fun x hx => (hφ x hx).symm) hOO
    have hLinφ : GammaLinearity.GammaLinear (rawSet Dv) (rawMap φ) (rawMap_vf φ Dv) s := by
      have h := linear_congr hfD hφVF (fun x hx => (hφ x hx).symm) s hLin
      intro x y hx hy
      exact h x y ((raw_vfSet D hDVF) ▸ hx) ((raw_vfSet D hDVF) ▸ hy)
    have hInjφ : Set.InjOn φ Dv := by
      intro x hx y hy he
      apply Subtype.ext
      apply hDInj hx hy
      exact (hφval x hx).symm.trans ((congrArg Subtype.val he).trans (hφval y hy))
    let E := f p '' D
    let Ev := vfSet E
    have hEVF : E ⊆ {x | iVF x} := by rintro _ ⟨x,hx,rfl⟩; exact hfD x hx
    have hE : PaperBalls.IsOpenBall E := (hOO D Set.Subset.rfl).mp hDOpen
    have hbij : Set.BijOn (f p) D E := ⟨fun x hx => ⟨x,hx,rfl⟩,hDInj,fun y hy => hy⟩
    have hBijφ : Set.BijOn φ Dv Ev := by
      refine ⟨?_,hInjφ,?_⟩
      · intro x hx
        change (φ x).val ∈ E
        rw [hφval x hx]
        exact ⟨x.val,hx,rfl⟩
      · intro y hy
        obtain ⟨x,hx,hxy⟩ := hy
        let X : VF (M := M) := ⟨x,hDVF hx⟩
        exact ⟨X,hx,Subtype.ext ((hφval X hx).trans hxy)⟩
    have hRawImage : rawSet (φ '' Dv) = E := raw_image_of_agrees D hDVF (f p) φ hφ
    have hFib : InverseDifferencePreparation.TranslatedFibres D (f p) (R p) := by
      intro a ha
      exact ⟨t,fun y => ⟨fun h => h.2,fun h => ⟨hDA ha,h⟩⟩⟩
    have finish (hSub : ∀ a ∈ Dv, translatedRV t (φ a) ⊆ Ev)
        (hCover : ∀ y ∈ Ev, ∃ a ∈ Dv, y ∈ translatedRV t (φ a)) :
        CellData (CellsFromFibres.relation Dv φ t) φ t := by
      have hImage : ∀ a ∈ D, ∀ y, ![a,y] ∈ R p → y ∈ E := by
        intro a ha y hy
        let X : VF (M := M) := ⟨a,hDVF ha⟩
        let Y : VF (M := M) := ⟨y,hy.2.1⟩
        exact hSub X ha ((hRow X Y ha).mp hy)
      obtain ⟨u,hu⟩ := InverseRowsOnBall.constant_on_body A hAVF f hfVF hInj R T hU
        hUniform b E hEVF hE hbij hOO hFib hImage
      apply CellsFromFibres.balanced Dv Ev φ u t hOne hPoly hBijφ hSub hCover hDo
        ((raw_vfSet E hEVF).symm ▸ hE) hOOφ s hLinφ
      intro a ha x hx hax
      have hh : ![a.val,(φ x).val] ∈ R p := (hRow a (φ x) ha).mpr hax
      rw [hφval x hx] at hh
      have he := hu a.val ha x.val hx hh
      rw [RVDifferencePairs.difference_vf a x] at he
      exact Subtype.ext he
    rcases hE with hWhole | ⟨c,β,hOrd⟩
    · apply finish
      · intro a ha y hy
        change y.val ∈ E
        exact hWhole.symm ▸ y.property
      · intro y hy
        obtain ⟨u,hu⟩ := CanonicalRV.encodedRv_surjective t
        let z := y-u
        have hz : z ∈ Ev := by
          change z.val ∈ E
          exact hWhole.symm ▸ z.property
        obtain ⟨a,ha,haz⟩ := hBijφ.2.2 hz
        refine ⟨a,ha,?_⟩
        change rv (y-φ a) = t
        rw [haz]
        have he : y-z = u := by dsimp [z]; ring
        rw [he]
        exact Subtype.ext (congrArg Subtype.val hu)
    · by_cases hLarge : Values.vrv t ≤ β.val
      · apply CellsFromFibres.separated Dv φ t hOne hPoly hInjφ hOOφ (↑β.val)
        · rw [hRawImage,hOrd]
          exact Or.inr (Or.inr ⟨c,β,true,rfl,rfl⟩)
        · exact WithBot.coe_le_coe.mpr hLarge
      · obtain ⟨hSub,hCover⟩ := TranslatedRVGeometry.cover_ordinary c β t (lt_of_not_ge hLarge)
        apply finish
        · intro a ha y hy
          have hfa := hBijφ.1 ha
          have hh := hSub (φ a) (hOrd ▸ hfa) ⟨y,hy,rfl⟩
          change y.val ∈ E
          exact hOrd.symm ▸ hh
        · intro y hy
          obtain ⟨z,hz,hyz⟩ := hCover y (hOrd ▸ hy)
          obtain ⟨a,ha,haz⟩ := hBijφ.2.2 (hOrd.symm ▸ hz)
          exact ⟨a,ha,haz.symm ▸ hyz⟩

end IntegrationInACVF.Section4.PreparedBodyCells
