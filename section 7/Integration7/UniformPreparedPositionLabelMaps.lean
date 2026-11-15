import Integration7.UniformBalancedCompatiblePreparations
import IntegrationSection5.RelativeLabelPreservation

/-! The actual compatible positioning preparations preserve the
entire old family label tuple on both VF and induced raw RV maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
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

def conjugateMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) : Map P.source P.target :=
  unaryConjugate P.sourceSpecial P.targetSpecial (F.positionMapExtended hNames P.baseInclusion)

theorem conjugate_bijective (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.conjugateMap :=
  unaryConjugate_bijective P.sourceSpecial P.targetSpecial _ (F.position_to_image_bijective hBalanced hNames)

def sourceOldLabelIndex (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Fin (m+F.arity) → Fin P.sourceArity := suffixIndex (special_chain_rvArity_le P.sourceSpecial.chain)

def targetOldLabelIndex (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Fin (m+F.arity) → Fin P.targetArity := suffixIndex (special_chain_rvArity_le P.targetSpecial.chain)

theorem conjugate_old_labels (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (a : P.source) (j : Fin (m+F.arity)) :
    (P.conjugateMap a).val.2 (P.targetOldLabelIndex j) = a.val.2 (P.sourceOldLabelIndex j) := by
  have hSource := special_oldLabels P.sourceSpecial (P.sourceSpecial.inverseMap a) j
  have he := congrArg (fun z : P.source => z.val.2 (P.sourceOldLabelIndex j)) (P.sourceSpecial.apply_inverse a)
  exact (special_oldLabels P.targetSpecial
    (F.positionMapExtended hNames P.baseInclusion (P.sourceSpecial.inverseMap a)) j).trans
      (hSource.symm.trans he)

def rawMap (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :=
  rvContractionMap P.conjugateMap P.forwardContractible

theorem raw_map_bijective (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    Function.Bijective P.rawMap :=
  rvContractionMap_bijective P.conjugateMap P.conjugate_bijective P.forwardContractible P.backwardContractible

theorem raw_map_gamma (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    GammaGraphDefinable G (rvPullbackMapGraph P.rawMap) :=
  gamma_rvContractionMap_graph P.conjugateMap P.forwardContractible P.conjugateGamma

theorem raw_map_old_labels (P : UniformBalancedPositionPreparation G C F hBalanced hNames)
    (u : rvObjectDomain (pullbackObject P.source)) (j : Fin (m+F.arity)) :
    (P.rawMap u).val (Fin.natAdd 1 (P.targetOldLabelIndex j)) =
      u.val (Fin.natAdd 1 (P.sourceOldLabelIndex j)) := by
  obtain ⟨a,rfl⟩ := rawKeyImage_surjective P.source u
  rw [rawMap,rvContractionMap_spec]
  exact (Fin.append_right _ _ _).trans ((P.conjugate_old_labels a j).trans (Fin.append_right _ _ _).symm)

end IntegrationInACVF.Section7.UniformBalancedPositionPreparation
