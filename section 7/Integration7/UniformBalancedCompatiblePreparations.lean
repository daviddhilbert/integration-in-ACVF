module

public import Integration7.UniformBalancedPositionPreparations
public import Integration7.UniformPreparedPositionGammaProducts
public import Integration7.SelectedBalancedParadigms

@[expose] public section

/-! Actual compatible preparations of the whole balanced positioning
family in one containing context, together with the proved Gamma product
calculation on its prepared points. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {m : ℕ}

structure UniformBalancedPositionPreparation (G : Base (M := M)) (C : BaseContext M)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) (hNames : commonRealNames G ⊆ (C.base : Set M)) where
  context : BaseContext M
  baseInclusion : (C.base : Set M) ⊆ (context.base : Set M)
  sourceArity : ℕ
  targetArity : ℕ
  source : DefSet (M := M) (context.base : Set M) 1 sourceArity
  target : DefSet (M := M) (context.base : Set M) 1 targetArity
  sourceSpecial : SpecialBijection
    (extendBase (VerticalOffsets.keyImage (gammaRVGraphRefinement A F.parameters hNames)) baseInclusion) source
  targetSpecial : SpecialBijection (extendBase (F.positionImage hNames) baseInclusion) target
  sourceGamma : GammaChainDefinable G sourceSpecial.chain
  targetGamma : GammaChainDefinable G targetSpecial.chain
  sourcePullback : IsRVPullback (carrier source)
  targetPullback : IsRVPullback (carrier target)
  forwardContractible : Contractible (unaryConjugate sourceSpecial targetSpecial (F.positionMapExtended hNames baseInclusion))
  backwardContractible : Contractible (Map.inverse
    (unaryConjugate sourceSpecial targetSpecial (F.positionMapExtended hNames baseInclusion))
    (unaryConjugate_bijective sourceSpecial targetSpecial _ (F.position_to_image_bijective hBalanced hNames)))
  conjugateGamma : GammaGraphDefinable G (pointMapGraph
    (unaryConjugate sourceSpecial targetSpecial (F.positionMapExtended hNames baseInclusion)))
  keyMap : Map (keyImage source) (keyImage target)
  keyBijective : Function.Bijective keyMap
  keySquare : ∀ a : source, keyMap (toKeyImage source a) = toKeyImage target
    (unaryConjugate sourceSpecial targetSpecial (F.positionMapExtended hNames baseInclusion) a)

theorem uniform_balanced_position_preparation_exists (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hBalanced : F.BalancedRows) : Nonempty (UniformBalancedPositionPreparation G C F hBalanced hNames) := by
  obtain ⟨D,hCD,r,s,K,E,TK,TE,hTK,hTE,hK,hE,hc,hback,hg,g,⟨hgb,hSquare⟩,_⟩ :=
    F.position_compatible_preparation_exists C hGC hNames γ hγ hγ1 hBalanced
  exact ⟨⟨D,hCD,r,s,K,E,TK,TE,hTK,hTE,hK,hE,hc,hback,hg,g,hgb,hSquare⟩⟩

namespace UniformBalancedPositionPreparation
variable {C : BaseContext M} {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

theorem gamma_products (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (hNonzero : ∀ b : A, (F.vertical.projection b).val.2 F.vertical.paradigm_index ≠ rv (0 : VF (M := M)))
    (a : P.source) (ha : vfAt a.val 0 ≠ 0) :
    ∃ b : A, ∃ r : RV (M := M),
      (P.sourceSpecial.inverseMap a).val.2 = Fin.append b.val.2 (F.parameters.toFun b) ∧
      Cells.IsBalanced (mixedPairFibre F.parameters b) (F.localPosition b) r
        ((F.vertical.projection b).val.2 F.vertical.paradigm_index) ∧
      Values.vrv r*Values.vfValueHom (vfAt
        (unaryConjugate P.sourceSpecial P.targetSpecial (F.positionMapExtended hNames P.baseInclusion) a).val 0) =
          Values.vfValueHom (vfAt a.val 0)*Values.vrv ((F.vertical.projection b).val.2 F.vertical.paradigm_index) :=
  F.prepared_position_gamma_products_over_extension hBalanced hNames P.baseInclusion hNonzero
    P.sourceSpecial P.targetSpecial P.sourcePullback P.targetPullback P.forwardContractible P.backwardContractible a ha

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
