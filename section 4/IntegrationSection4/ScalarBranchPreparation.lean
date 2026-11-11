import IntegrationSection4.PositionRows
import IntegrationSection4.GammaDomainPreparation

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

namespace IntegrationInACVF.Section4.ScalarBranchPreparation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem constant_branch {κ : Cardinal} (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (G : GammaParameters.Base (M := M)) (hsmall : Cardinal.mk G.real < κ)
    (hGenerated : VFGammaGeneratedBase G) {m d : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f) (j : Fin m)
    (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    (hConst : ∀ p x, x ∈ A p → ∀ y, y ∈ A p → e p x = e p y → f p x = f p y) :
    ∃ q : ℕ, ∃ Q : GammaRVMap G (GammaFamilySyntax.domain A) q,
      (∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val) ∧
      ∀ a, Nonempty (PositionRow Q a f j) := by
  let A' := FamilyRefinementDomains.domain A e
  let f' : (Fin (m+d) → M) → M → M := FamilyRefinementDomains.function f
  have hf' := FamilyRefinementDomains.graph_definable (GammaBaseBridge.fullBase G) A f e hf he
  have hDom := GammaFamilySyntax.domain_definable G A'
    (FiniteScalarFamilies.domain_definable (GammaBaseBridge.fullBase G) A' f' hf')
  obtain ⟨l,E,T,hE⟩ := GammaDomainPreparation.prepare hs h00 G hsmall hGenerated _ hDom
  let Q := GammaRVMap.preparedRefinement G A e he T
  refine ⟨1+l,Q,fun a b h => GammaRVMap.preparedRefinement_reflects_rv G A e he T a b h,?_⟩
  intro a₀
  apply PositionRow.of_preparation A hAVF f hfVF j e he T
  intro b φ hφ hPoly
  let p := GammaFamilySyntax.labels (T.special.inverseMap b).val
  let D := InverseBodies.body T.special b
  have hDA : D ⊆ A' p := FamilyPreparedLinearity.body_subset A' T.special T.source_eq b
  apply CellsFromFibres.constant (ScalarPositioning.vfSet D) φ
    ((T.special.inverseMap b).val.2 (Fin.castAdd d j)) (InverseOneCells.one_cell T.special
      (T.target_eq.symm ▸ hE) b) hPoly
  intro x hx y hy
  apply Subtype.ext
  rw [← Cells.rawMap_on φ x,← Cells.rawMap_on φ y,hφ _ hx,hφ _ hy]
  exact FamilyRefinementDomains.constant A f e hConst p x.val y.val (hDA hx) (hDA hy)

theorem injective_branch {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) {m d : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f) (j : Fin m)
    (e : (Fin m → M) → M → Fin d → M)
    (he : FamilyPositionRefinement.RVRefinement (GammaBaseBridge.fullBase G) A e)
    (hRef : ∀ p x, x ∈ A p → ∀ y, y ∈ A p → f p x = f p y → e p x = e p y → x = y) :
    ∃ q : ℕ, ∃ Q : GammaRVMap G (GammaFamilySyntax.domain A) q,
      (∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val) ∧
      ∀ a, Nonempty (PositionRow Q a f j) := by
  let A' := FamilyRefinementDomains.domain A e
  let f' : (Fin (m+d) → M) → M → M := FamilyRefinementDomains.function f
  let j' : Fin (m+d) := Fin.castAdd d j
  have hA'VF : ∀ p, A' p ⊆ {x | iVF x} := fun p x hx => hAVF _ hx.1
  have hf'VF : ∀ p x, x ∈ A' p → iVF (f' p x) := fun p x hx => hfVF _ x hx.1
  have hf' := FamilyRefinementDomains.graph_definable (GammaBaseBridge.fullBase G) A f e hf he
  have hInj' : ∀ p, Set.InjOn (f' p) (A' p) := FamilyRefinementDomains.injective A f e hRef
  let R := TranslatedFamilySyntax.relation A' f' j'
  have hR := TranslatedFamilySyntax.definable (GammaBaseBridge.fullBase G) A' f' j' hf'
  have hr := FamilyInverseDifferences.relation_definable G A' f' R hR hf'
  obtain ⟨l,E,T,hE,hUniform,hProps⟩ := FamilyJointPreparation.prepare hκ hs h00 G hsmall
    hGenerated δ hδ hδ1 A' hA'VF f' hf'VF hf' hInj' (FamilyInverseDifferences.relation A' f' R) hr
  let Q := GammaRVMap.preparedRefinement G A e he T
  refine ⟨1+l,Q,fun a b h => GammaRVMap.preparedRefinement_reflects_rv G A e he T a b h,?_⟩
  intro a₀
  apply PositionRow.of_preparation A hAVF f hfVF j e he T
  intro b φ hφ hPoly
  obtain ⟨⟨s,hLin⟩,hOO⟩ := hProps b
  exact PreparedBodyCells.cell A' hA'VF f' hf'VF hInj' j' T.special T.source_eq
    (T.target_eq.symm ▸ hE) hUniform b φ hφ s hLin hOO hPoly

end IntegrationInACVF.Section4.ScalarBranchPreparation
