import IntegrationSection4.InverseDifferenceSyntax
import IntegrationSection4.InverseDifferenceGeometry
import IntegrationSection4.InverseBodies

/-! Lemma 4.4 over the original Gamma base, using actual partial inverses
and translated RV fibres. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF

namespace IntegrationInACVF.Section4.InverseDifferencePreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Each vertical fibre is exactly a translate of an actual RV fibre.
On the VF sort `difference b (f a)` is `rv (b-f a)`. -/
def TranslatedFibres (A : Set M) (f : M → M) (R : Set (Fin 2 → M)) : Prop :=
  ∀ a ∈ A, ∃ t : RV (M := M), ∀ b,
    ![a,b] ∈ R ↔ iVF b ∧ RVDifferencePairs.difference b (f a) = t.val

def differenceValues (A : Set M) (f : M → M) (R : Set (Fin 2 → M)) (E : Set M) : Set M :=
  {t | ∃ a ∈ E, ∃ b, ![a,b] ∈ R ∧ t = RVDifferencePairs.difference a (RVInverse.inverse A f b)}

theorem fibre_nonempty (A B : Set M) (hBVF : B ⊆ {x | iVF x})
    (f : M → M) (hbij : Set.BijOn f A B) (R : Set (Fin 2 → M))
    (hFib : TranslatedFibres A f R) (a : M) (ha : a ∈ A) :
    ∃ b, ![a,b] ∈ R := by
  obtain ⟨t,ht⟩ := hFib a ha
  obtain ⟨x,hx⟩ := CanonicalRV.encodedRv_surjective t
  let fa : VFType (M := M) := ⟨f a,hBVF (hbij.1 ha)⟩
  refine ⟨(x+fa).val,(ht _).mpr ⟨(x+fa).property,?_⟩⟩
  rw [RVDifferencePairs.difference_vf (x+fa) fa,add_sub_cancel_right]
  exact congrArg Subtype.val hx

theorem row_single_valued (A B : Set M) (hAVF : A ⊆ {x | iVF x})
    (hBVF : B ⊆ {x | iVF x}) (hB : PaperBalls.IsOpenBall B)
    (f : M → M) (hbij : Set.BijOn f A B) (hoo : MaximalOpenClasses.OpenToOpen A f)
    (R : Set (Fin 2 → M)) (hSub : ∀ z ∈ R, z 0 ∈ A ∧ z 1 ∈ B)
    (hFib : TranslatedFibres A f R) (a t u : M)
    (ht : InverseDifferenceSyntax.row A f R ![a,t])
    (hu : InverseDifferenceSyntax.row A f R ![a,u]) : t = u := by
  obtain ⟨w,hw,hwf,hwt⟩ := ht
  obtain ⟨v,hv,hvf,hvu⟩ := hu
  have ha := (hSub ![a,w 0] hw).1
  have hb := (hSub ![a,w 0] hw).2
  have hc := (hSub ![a,v 0] hv).2
  obtain ⟨s,hs⟩ := hFib a ha
  have hbc := ((hs _).mp hw).2.trans ((hs _).mp hv).2.symm
  have he := InverseDifferenceGeometry.inverse_differences A B hAVF hBVF hB f hbij hoo
    ⟨a,hAVF ha⟩ ⟨w 0,hBVF hb⟩ ⟨v 0,hBVF hc⟩ ha hb hc hbc
  have hiw : RVInverse.inverse A f (w 0) = w 1 := by
    rw [hwf.2]
    exact RVInverse.inverse_on hbij.2.1 hwf.1
  have hiv : RVInverse.inverse A f (v 0) = v 1 := by
    rw [hvf.2]
    exact RVInverse.inverse_on hbij.2.1 hvf.1
  rw [hiw,hiv] at he
  exact hwt.trans (he.trans hvu.symm)

theorem lemma_4_4 {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) (A B : Set M)
    (hA : DefinableAtBase G .vf A) (hBVF : B ⊆ {x | iVF x})
    (hB : PaperBalls.IsOpenBall B) (f : M → M)
    (hf : DefinableOverBase G (fun _ : Fin 2 => .vf) (ImaginaryBaseImages.graphOn A f))
    (hbij : Set.BijOn f A B) (hoo : MaximalOpenClasses.OpenToOpen A f)
    (R : Set (Fin 2 → M)) (hR : DefinableOverBase G (fun _ => .vf) R)
    (hSub : ∀ z ∈ R, z 0 ∈ A ∧ z 1 ∈ B) (hFib : TranslatedFibres A f R) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
      ∃ T : GammaSpecialBijection G (GammaUnarySyntax.pointSet A) E,
        IsRVPullback E ∧ ∀ b : T.target, ∃ t : RV (M := M),
          differenceValues A f R (InverseBodies.body T.special b) = {t.val} := by
  obtain ⟨l,E,T,hE,hUniform⟩ := UnaryPreparation.prepare hs h00 G hsmall hGenerated A hA
    (InverseDifferenceSyntax.relation A f R) (InverseDifferenceSyntax.relation_definable G A hA f R hR hf)
  refine ⟨l,E,T,hE,?_⟩
  intro b
  let a₀ := T.special.inverseMap b
  let a := (vfAt a₀.val 0).val
  have ha : a ∈ A := (Set.ext_iff.mp T.source_eq a₀.val).mp a₀.property
  obtain ⟨c,hc⟩ := fibre_nonempty A B hBVF f hbij R hFib a ha
  obtain ⟨x,hx,hxc⟩ := hbij.2.2 ((hSub ![a,c] hc).2)
  change f x = c at hxc
  let t := RVDifferencePairs.difference a x
  have htRow : InverseDifferenceSyntax.row A f R ![a,t] := ⟨![c,x],hc,⟨hx,hxc.symm⟩,rfl⟩
  have htRV : iRV t := (InverseDifferenceSyntax.row_proper A hA.proper f R hR.proper ![a,t] htRow).2
  refine ⟨⟨t,htRV⟩,Set.ext fun u => ?_⟩
  constructor
  · rintro ⟨d,⟨d₀,hd,hdKey⟩,e,hde,hue⟩
    have hdA : d ∈ A := by
      have hh := (Set.ext_iff.mp T.source_eq d₀.val).mp d₀.property
      change (vfAt d₀.val 0).val ∈ A at hh
      rwa [hd] at hh
    have heB := (hSub ![d,e] hde).2
    have heI : e ∈ f '' A := hbij.image_eq.symm ▸ heB
    have hInv := RVInverse.inverse_right heI
    have huRow : InverseDifferenceSyntax.row A f R ![d,u] :=
      ⟨![e,RVInverse.inverse A f e],hde,⟨hInv.1,hInv.2.symm⟩,hue⟩
    let q : Point (M := M) 0 1 := (Fin.elim0,![⟨t,htRV⟩])
    have hConst := hUniform (T.special.toMap d₀) b hdKey q
    rw [T.special.inverse_apply] at hConst
    have hdRow : InverseDifferenceSyntax.row A f R ![d,t] := by
      have hh := hConst.mpr htRow
      change InverseDifferenceSyntax.row A f R ![(vfAt d₀.val 0).val,t] at hh
      rwa [hd] at hh
    exact row_single_valued A B hA.proper hBVF hB f hbij hoo R hSub hFib d u t huRow hdRow
  · intro hu
    change u = t at hu
    refine ⟨a,⟨a₀,rfl,by rw [T.special.apply_inverse]; rfl⟩,c,hc,?_⟩
    rw [hu,← hxc,RVInverse.inverse_on hbij.2.1 hx]

end IntegrationInACVF.Section4.InverseDifferencePreparation
