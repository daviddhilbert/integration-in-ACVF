module

public import Integration7.MatchingPreparedFamilyDomains

@[expose] public section

/-! The whole balanced graph with both compatible prepared keys.
Its matching and different refinements are actual subsets, and membership
of a graph point is exactly membership of its original source point. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformBalancedPositionPreparation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

def wholePreparedPairFamily (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  gammaRVGraphRefinement (gammaRVGraphRefinement A F.parameters hNames) P.pairKeyLabels hNames

theorem whole_prepared_pair_family_gamma
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaSetDefinable G (carrier P.wholePreparedPairFamily) :=
  gamma_rv_graph_refinement_target_gamma _ P.pairKeyLabels hNames

theorem whole_prepared_pair_family_finite_labels
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M), {r | (x,r) ∈ carrier P.wholePreparedPairFamily}.Finite :=
  gamma_rv_graph_refinement_finite_labels _
    (gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames) P.pairKeyLabels hNames

theorem matching_prepared_subset_whole
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    carrier P.matchingPreparedFamily ⊆ carrier P.wholePreparedPairFamily := by
  rintro q ⟨p,hp⟩
  let a : gammaRVGraphRefinement A F.parameters hNames :=
    ⟨p.val,by obtain ⟨a,ha,_⟩ := p.property; exact ha ▸ a.property⟩
  exact ⟨a,hp⟩

theorem different_prepared_subset_whole
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    carrier P.differentPreparedFamily ⊆ carrier P.wholePreparedPairFamily := by
  rintro q ⟨p,hp⟩
  exact ⟨⟨p.val,p.property.1⟩,hp⟩

theorem matching_prepared_graph_mem
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : gammaRVGraphRefinement A F.parameters hNames) :
    (gammaRVGraphRefinementMap _ P.pairKeyLabels hNames a).val ∈ carrier P.matchingPreparedFamily ↔
      a.val ∈ P.matchingPart := by
  constructor
  · rintro ⟨p,hp⟩
    let b : gammaRVGraphRefinement A F.parameters hNames :=
      ⟨p.val,by obtain ⟨a,ha,_⟩ := p.property; exact ha ▸ a.property⟩
    have hGraph : gammaRVGraphRefinementMap _ P.pairKeyLabels hNames b =
        gammaRVGraphRefinementMap _ P.pairKeyLabels hNames a := Subtype.ext hp
    have he := gamma_rv_graph_refinement_injective _ P.pairKeyLabels hNames hGraph
    exact Eq.mp (congrArg (fun q : gammaRVGraphRefinement A F.parameters hNames =>
      q.val ∈ P.matchingPart) he) p.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,rfl⟩

theorem different_prepared_graph_mem
    (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : gammaRVGraphRefinement A F.parameters hNames) :
    (gammaRVGraphRefinementMap _ P.pairKeyLabels hNames a).val ∈ carrier P.differentPreparedFamily ↔
      a.val ∉ P.matchingPart := by
  constructor
  · rintro ⟨p,hp⟩
    let b : gammaRVGraphRefinement A F.parameters hNames := ⟨p.val,p.property.1⟩
    have hGraph : gammaRVGraphRefinementMap _ P.pairKeyLabels hNames b =
        gammaRVGraphRefinementMap _ P.pairKeyLabels hNames a := Subtype.ext hp
    have he := gamma_rv_graph_refinement_injective _ P.pairKeyLabels hNames hGraph
    exact Eq.mp (congrArg (fun q : gammaRVGraphRefinement A F.parameters hNames =>
      q.val ∉ P.matchingPart) he) p.property.2
  · intro ha
    exact ⟨⟨a.val,a.property,ha⟩,rfl⟩

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
