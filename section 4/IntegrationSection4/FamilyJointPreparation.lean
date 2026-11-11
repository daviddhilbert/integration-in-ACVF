import IntegrationSection4.FamilyLinearPreparation
import IntegrationSection4.FamilyInverseDifferences

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

namespace IntegrationInACVF.Section4.FamilyJointPreparation

open GammaFamilySyntax

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem body_subset_of_refines {S : Set M} {m l q : ℕ}
    {A : DefSet (M := M) S 1 m} {B : DefSet (M := M) S 1 l} {C : DefSet (M := M) S 1 q}
    (T : SpecialBijection A B) (W : SpecialBijection A C)
    (hRef : FiniteRelationPreparation.Refines T W) (c : C) :
    InverseBodies.body W c ⊆ InverseBodies.body T (T.toMap (W.inverseMap c)) := by
  rintro x ⟨a,ha,he⟩
  have hh := hRef (W.toMap a) c he
  rw [W.inverse_apply] at hh
  exact ⟨a,ha,hh⟩

/-- Further original-base relation preparation preserves the uniform
linearity and open-to-open conclusions on every actual inverse piece. -/
theorem prepare {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) {m k : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f)
    (hInj : ∀ p, Set.InjOn (f p) (A p))
    (r : Point (M := M) 1 m → Point (M := M) 0 k → Prop) (hr : GammaGraphDefinable G r) :
    ∃ l : ℕ, ∃ E : Set (Point (M := M) 1 l),
    ∃ T : GammaSpecialBijection G (domain A) E,
      IsRVPullback E ∧ FiniteRelationPreparation.Uniform r T.special ∧
      ∀ b : T.target,
        (∃ s : Values.Gamma (M := M), GammaLinearity.GammaLinear (InverseBodies.body T.special b)
          (f (labels (T.special.inverseMap b).val))
          (fun x hx => hfVF _ x (FamilyPreparedLinearity.body_subset A T.special T.source_eq b hx)) s) ∧
        MaximalOpenClasses.OpenToOpen (InverseBodies.body T.special b)
          (f (labels (T.special.inverseMap b).val)) := by
  obtain ⟨l,E,T,hE,hProps⟩ := FamilyLinearPreparation.prepare hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 A hAVF f hfVF hf hInj
  obtain ⟨q,F,U,hAlt,hUG,hF,hR⟩ := GammaRelationPreparation.prepare_after hs h00 G hsmall
    hGenerated T.real_contains T.special T.invariant_graphs r hr
  let W := T.special.comp U hAlt
  have hWG := GammaRelationPreparation.chain_append_definable T.special.chain U.chain T.invariant_graphs hUG
  let V : GammaSpecialBijection G (domain A) (carrier F) :=
    ⟨T.codes,T.real_contains,T.source,F,T.source_eq,rfl,W,hWG⟩
  refine ⟨q,carrier F,V,hF,hR,?_⟩
  intro c
  let b := T.special.toMap (W.inverseMap c)
  have hSub := body_subset_of_refines T.special W
    (FiniteRelationPreparation.refines_comp T.special U hAlt) c
  obtain ⟨⟨s,hLin⟩,hOO⟩ := hProps b
  have hp : labels (T.special.inverseMap b).val = labels (W.inverseMap c).val := by
    rw [SpecialBijection.inverse_apply]
  have hfEq := congrArg f hp
  rw [hfEq] at hOO
  refine ⟨⟨s,?_⟩,?_⟩
  · intro x y hx hy
    have hh := hLin x y (hSub hx) (hSub hy)
    have hfx : (⟨f (labels (T.special.inverseMap b).val) x.val,
        hfVF _ _ (FamilyPreparedLinearity.body_subset A T.special T.source_eq b (hSub hx))⟩ : VFType (M := M)) =
        ⟨f (labels (W.inverseMap c).val) x.val,
          hfVF _ _ (FamilyPreparedLinearity.body_subset A W T.source_eq c hx)⟩ :=
      Subtype.ext (congrFun hfEq x.val)
    have hfy : (⟨f (labels (T.special.inverseMap b).val) y.val,
        hfVF _ _ (FamilyPreparedLinearity.body_subset A T.special T.source_eq b (hSub hy))⟩ : VFType (M := M)) =
        ⟨f (labels (W.inverseMap c).val) y.val,
          hfVF _ _ (FamilyPreparedLinearity.body_subset A W T.source_eq c hy)⟩ :=
      Subtype.ext (congrFun hfEq y.val)
    change Values.vfValueHom ((_ : VFType (M := M))-(_ : VFType (M := M))) = _ at hh ⊢
    rwa [hfx,hfy] at hh
  · intro Q hQ
    exact hOO Q (hQ.trans hSub)

end IntegrationInACVF.Section4.FamilyJointPreparation
