import IntegrationSection4.ScalarBranchPreparation
import IntegrationSection4.PositionRowTransport

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

namespace IntegrationInACVF.Section4.ScalarPositionDecomposition

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A single finite-arity original-base RV map prepares all scalar
positioning rows. Its fibres have complete row descriptions and the
constant/separated/balanced cell constructions, once their original
RV-polydisc containment is supplied. -/
theorem exists_map {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ) {m : ℕ}
    (A : (Fin m → M) → Set M) (hAVF : ∀ p, A p ⊆ {x | iVF x})
    (f : (Fin m → M) → M → M) (hfVF : ∀ p x, x ∈ A p → iVF (f p x))
    (hf : FiniteScalarFamilies.Graph (GammaBaseBridge.fullBase G) A f) (j : Fin m) :
    ∃ q : ℕ, ∃ Q : GammaRVMap G (GammaFamilySyntax.domain A) q,
      (∀ a b, Q.toFun a = Q.toFun b → SameRV a.val b.val) ∧
      ∀ a, Nonempty (PositionRow Q a f j) := by
  let B := GammaBaseBridge.fullBase G
  let L (p : Fin m → M) := LocalConstancySyntax.locus (A p) (f p)
  let O (p : Fin m → M) := A p \ L p
  have hL := FamilyLocalConstancy.locus_definable B A f hf
  have hLA : ∀ p, L p ⊆ A p := fun p => LocalConstancySyntax.subset (A p) (f p)
  have hGraphL := FiniteScalarFamilies.restrict B A L f hf hL hLA
  have hOff := FullBaseAtomicity.OverBase.inter (FiniteScalarFamilies.domain_definable B A f hf) hL.compl
  have hGraphO := FiniteScalarFamilies.restrict B A O f hf hOff (fun _ _ h => h.1)
  obtain ⟨d₀,e₀,d₁,e₁,he₀,hConst,he₁,hInject⟩ :=
    FamilyPositionRefinement.constant_or_injective hκ hs h00 B hsmall δ hδ1 A hAVF f hfVF hf
  obtain ⟨q₀,Q₀,hRV₀,hRows₀⟩ := ScalarBranchPreparation.constant_branch hs h00 G hsmall hGenerated
    L (fun p x hx => hAVF p (hLA p hx)) f (fun p x hx => hfVF p x (hLA p hx)) hGraphL j e₀ he₀ hConst
  obtain ⟨q₁,Q₁,hRV₁,hRows₁⟩ := ScalarBranchPreparation.injective_branch hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 O (fun p x hx => hAVF p hx.1) f (fun p x hx => hfVF p x hx.1) hGraphO j e₁ he₁ hInject
  let D := GammaFamilySyntax.domain A
  let D₀ := GammaFamilySyntax.domain L
  let D₁ := GammaFamilySyntax.domain O
  have hDis : Disjoint D₀ D₁ := Set.disjoint_left.mpr (fun p hp hq => hq.2 hp)
  have hCover : D ⊆ D₀ ∪ D₁ := by
    intro p hp
    by_cases h : (vfAt p 0).val ∈ L (GammaFamilySyntax.labels p)
    · exact Or.inl h
    · exact Or.inr ⟨hp,h⟩
  have hSub : D₀ ∪ D₁ ⊆ D := by
    intro p hp
    rcases hp with h | h
    · exact hLA _ h
    · exact h.1
  have hD := GammaFamilySyntax.domain_definable G A (FiniteScalarFamilies.domain_definable B A f hf)
  let J := GammaRVMap.join Q₀ Q₁ hDis
  let Q := J.restrict D hCover hD
  refine ⟨1+(q₀+q₁),Q,?_,?_⟩
  · intro a b he
    exact GammaRVMap.join_reflects_rv Q₀ Q₁ hDis hRV₀ hRV₁
      ⟨a.val,hCover a.property⟩ ⟨b.val,hCover b.property⟩ he
  · intro a₀
    have hfibre := GammaRVMap.restrict_same_fibre J D hCover hD hSub a₀
    by_cases h : a₀.val ∈ D₀
    · let b₀ : D₀ := ⟨a₀.val,h⟩
      obtain ⟨row⟩ := hRows₀ b₀
      have hF : {p | ∃ a : D, a.val = p ∧ Q.toFun a = Q.toFun a₀} =
          {p | ∃ a : D₀, a.val = p ∧ Q₀.toFun a = Q₀.toFun b₀} :=
        hfibre.trans (GammaRVMap.join_left_fibre Q₀ Q₁ hDis b₀)
      exact ⟨row.transport hF rfl⟩
    · have h₁ : a₀.val ∈ D₁ := (hCover a₀.property).resolve_left h
      let b₀ : D₁ := ⟨a₀.val,h₁⟩
      obtain ⟨row⟩ := hRows₁ b₀
      have hF : {p | ∃ a : D, a.val = p ∧ Q.toFun a = Q.toFun a₀} =
          {p | ∃ a : D₁, a.val = p ∧ Q₁.toFun a = Q₁.toFun b₀} :=
        hfibre.trans (GammaRVMap.join_right_fibre Q₀ Q₁ hDis b₀)
      exact ⟨row.transport hF rfl⟩

end IntegrationInACVF.Section4.ScalarPositionDecomposition
