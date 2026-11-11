import IntegrationSection4.InverseDifferencePreparation
import IntegrationSection4.FamilyJointPreparation

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
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseRowsOnBall

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Restrict the inverse computation to an actual open image ball. The
ambient partial graph may have a larger injective domain. -/
theorem single_valued (A D E : Set M) (hDVF : D ⊆ {x | iVF x})
    (hEVF : E ⊆ {x | iVF x}) (hE : PaperBalls.IsOpenBall E) (hDA : D ⊆ A)
    (f : M → M) (hInj : Set.InjOn f A) (hbij : Set.BijOn f D E)
    (hoo : MaximalOpenClasses.OpenToOpen D f) (R : Set (Fin 2 → M))
    (a : M) (ha : a ∈ D) (t : RV (M := M))
    (hFib : ∀ b, ![a,b] ∈ R ↔ iVF b ∧ RVDifferencePairs.difference b (f a) = t.val)
    (hImage : ∀ b, ![a,b] ∈ R → b ∈ E) (u v : M)
    (hu : InverseDifferenceSyntax.row A f R ![a,u])
    (hv : InverseDifferenceSyntax.row A f R ![a,v]) : u = v := by
  obtain ⟨w,hw,hwf,hwu⟩ := hu
  obtain ⟨z,hz,hzf,hzv⟩ := hv
  have hb := hImage (w 0) hw
  have hc := hImage (z 0) hz
  have hwD : w 1 ∈ D := by
    obtain ⟨x,hx,hfx⟩ := hbij.2.2 hb
    have he : x = w 1 := hInj (hDA hx) hwf.1 (hfx.trans hwf.2)
    exact he ▸ hx
  have hzD : z 1 ∈ D := by
    obtain ⟨x,hx,hfx⟩ := hbij.2.2 hc
    have he : x = z 1 := hInj (hDA hx) hzf.1 (hfx.trans hzf.2)
    exact he ▸ hx
  have hbc := ((hFib _).mp hw).2.trans ((hFib _).mp hz).2.symm
  have he := InverseDifferenceGeometry.inverse_differences D E hDVF hEVF hE f hbij hoo
    ⟨a,hDVF ha⟩ ⟨w 0,hEVF hb⟩ ⟨z 0,hEVF hc⟩ ha hb hc hbc
  have hwInv : RVInverse.inverse D f (w 0) = w 1 := by
    rw [hwf.2]
    exact RVInverse.inverse_on hbij.2.1 hwD
  have hzInv : RVInverse.inverse D f (z 0) = z 1 := by
    rw [hzf.2]
    exact RVInverse.inverse_on hbij.2.1 hzD
  rw [hwInv,hzInv] at he
  exact hwu.trans (he.trans hzv.symm)

/-- Uniform preparation of the ambient inverse relation gives one actual
RV difference on a whole inverse piece whenever its vertical fibres stay
inside that piece's positioning image. -/
theorem constant_on_body {S : Set M} {m l : ℕ}
    {U : DefSet (M := M) S 1 m} {V : DefSet (M := M) S 1 l}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hInj : ∀ p, Set.InjOn (f p) (A p))
    (R : (Fin m → M) → Set (Fin 2 → M)) (T : SpecialBijection U V)
    (hU : carrier U = GammaFamilySyntax.domain A)
    (hUniform : FiniteRelationPreparation.Uniform (FamilyInverseDifferences.relation A f R) T)
    (b : V) (E : Set M) (hEVF : E ⊆ {x | iVF x}) (hE : PaperBalls.IsOpenBall E)
    (hbij : Set.BijOn (f (GammaFamilySyntax.labels (T.inverseMap b).val)) (InverseBodies.body T b) E)
    (hoo : MaximalOpenClasses.OpenToOpen (InverseBodies.body T b)
      (f (GammaFamilySyntax.labels (T.inverseMap b).val)))
    (hFib : InverseDifferencePreparation.TranslatedFibres (InverseBodies.body T b)
      (f (GammaFamilySyntax.labels (T.inverseMap b).val)) (R (GammaFamilySyntax.labels (T.inverseMap b).val)))
    (hImage : ∀ a ∈ InverseBodies.body T b, ∀ y,
      ![a,y] ∈ R (GammaFamilySyntax.labels (T.inverseMap b).val) → y ∈ E) :
    ∃ t : RV (M := M), ∀ a ∈ InverseBodies.body T b, ∀ x ∈ InverseBodies.body T b,
      ![a,f (GammaFamilySyntax.labels (T.inverseMap b).val) x] ∈ R (GammaFamilySyntax.labels (T.inverseMap b).val) →
        RVDifferencePairs.difference a x = t.val := by
  let p := GammaFamilySyntax.labels (T.inverseMap b).val
  let D := InverseBodies.body T b
  have hDA : D ⊆ A p := FamilyPreparedLinearity.body_subset A T hU b
  have hDVF : D ⊆ {x | iVF x} := fun x hx => hAVF p (hDA hx)
  let a₀ := T.inverseMap b
  let a := (vfAt a₀.val 0).val
  have ha : a ∈ D := ⟨a₀,rfl,by rw [T.apply_inverse]; rfl⟩
  obtain ⟨y,hy⟩ := InverseDifferencePreparation.fibre_nonempty D E hEVF (f p) hbij (R p) hFib a ha
  obtain ⟨x,hx,hfx⟩ := hbij.2.2 (hImage a ha y hy)
  let t := RVDifferencePairs.difference a x
  have htRV : iRV t := by
    change iRV (RVDifferencePairs.difference a x)
    rw [RVDifferencePairs.difference_vf (⟨a,hDVF ha⟩ : VFType (M := M)) ⟨x,hDVF hx⟩]
    let A₀ : VFType (M := M) := ⟨a,hDVF ha⟩
    let X₀ : VFType (M := M) := ⟨x,hDVF hx⟩
    exact rv_mem hM (A₀-X₀).property
  have hBase : InverseDifferenceSyntax.row (A p) (f p) (R p) ![a,t] :=
    ⟨![y,x],hy,⟨hDA hx,hfx.symm⟩,rfl⟩
  refine ⟨⟨t,htRV⟩,?_⟩
  intro c hc z hz hcz
  obtain ⟨c₀,hcVal,hcKey⟩ := hc
  let q : Point (M := M) 0 1 := (Fin.elim0,![⟨t,htRV⟩])
  have hh := hUniform (T.toMap c₀) b hcKey q
  rw [T.inverse_apply] at hh
  have hcLabels := FamilyPreparedLinearity.source_labels T c₀ b hcKey
  have hcRow : InverseDifferenceSyntax.row (A p) (f p) (R p) ![c,t] := by
    have h := hh.mpr hBase
    change InverseDifferenceSyntax.row (A (GammaFamilySyntax.labels c₀.val))
      (f (GammaFamilySyntax.labels c₀.val)) (R (GammaFamilySyntax.labels c₀.val))
      ![(vfAt c₀.val 0).val,t] at h
    rwa [hcLabels,hcVal] at h
  have hGiven : InverseDifferenceSyntax.row (A p) (f p) (R p)
      ![c,RVDifferencePairs.difference c z] := ⟨![f p z,z],hcz,⟨hDA hz,rfl⟩,rfl⟩
  have hcD : c ∈ D := ⟨c₀,hcVal,hcKey⟩
  obtain ⟨v,hv⟩ := hFib c hcD
  exact single_valued (A p) D E hDVF hEVF hE hDA (f p) (hInj p) hbij hoo (R p)
    c hcD v hv (hImage c hcD) _ _ hGiven hcRow

end IntegrationInACVF.Section4.InverseRowsOnBall
