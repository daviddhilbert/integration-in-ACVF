import Integration7.UniformPreparedPairKeys
import Integration7.GammaSpecialCommonNames
import IntegrationSection5.QuotientBijection

/-! Compatible positioning preparations can use the prescribed small
common-name context itself. Re-presenting their actual Gamma chains
changes no point values or inverse fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
variable {G : Base (M := M)} {m : ℕ} {C : BaseContext M}
variable {A : DefSet (M := M) (C.base : Set M) 2 m}
variable {F : UniformMixedCellPresentation G (carrier A)} {hBalanced : F.BalancedRows}
variable {hNames : commonRealNames G ⊆ (C.base : Set M)}

namespace UniformBalancedPositionPreparation

def inFixedContext (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    UniformBalancedPositionPreparation G C F hBalanced hNames := by
  let TA := gammaSpecialPresentation P.sourceSpecial P.sourceGamma hNames
  let TB := gammaSpecialPresentation P.targetSpecial P.targetGamma hNames
  have hTA : (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ TA.toMap) = (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ P.sourceSpecial.toMap) := by
    funext p
    apply Subtype.ext
    exact gamma_chain_presentation_apply P.sourceSpecial.chain P.sourceGamma hNames p
  have hTB : (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ TB.toMap) = (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ P.targetSpecial.toMap) := by
    funext p
    apply Subtype.ext
    exact gamma_chain_presentation_apply P.targetSpecial.chain P.targetGamma hNames p
  have hTAi : (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ TA.inverseMap) = (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ P.sourceSpecial.inverseMap) := by
    funext p
    apply P.sourceSpecial.bijective.1
    exact ((congrFun hTA (TA.inverseMap p)).symm.trans (TA.apply_inverse p)).trans
      (P.sourceSpecial.apply_inverse p).symm
  let f := F.positionMapExtended hNames (Set.Subset.refl (C.base : Set M))
  let g := unaryConjugate TA TB f
  have hG : (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ g) = (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ P.conjugateMap) := by
    funext p
    change TB.toMap (f (TA.inverseMap p)) = P.targetSpecial.toMap
      (F.positionMapExtended hNames P.baseInclusion (P.sourceSpecial.inverseMap p))
    rw [hTB,hTAi]
    rfl
  have hg : Function.Bijective g :=
    unaryConjugate_bijective TA TB f (F.position_to_image_bijective hBalanced hNames)
  have hForward : Contractible g := by
    intro p q hpq
    have h := P.forwardContractible p q hpq
    change SameRV (P.conjugateMap p).val (P.conjugateMap q).val at h
    rw [← hG] at h
    exact h
  have hInverse : (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ (Map.inverse g hg)) = (@SpecialTransformations.DefinableGeometry.Map.toFun LRV M N _ _ _ _ _ (Map.inverse P.conjugateMap P.conjugate_bijective)) := by
    funext p
    apply P.conjugate_bijective.1
    exact ((congrFun hG (Map.inverse g hg p)).symm.trans (Map.apply_inverse g hg p)).trans
      (Map.apply_inverse P.conjugateMap P.conjugate_bijective p).symm
  have hBackward : Contractible (Map.inverse g hg) := by
    intro p q hpq
    have h := P.backwardContractible p q hpq
    change SameRV (Map.inverse P.conjugateMap P.conjugate_bijective p).val
      (Map.inverse P.conjugateMap P.conjugate_bijective q).val at h
    rw [← hInverse] at h
    exact h
  have hGamma : GammaGraphDefinable G (pointMapGraph g) := by
    apply GammaGraphDefinable.congr P.conjugateGamma
    intro p q
    constructor
    · rintro ⟨a,ha,hq⟩
      exact ⟨a,ha,(congrArg Subtype.val (congrFun hG a)).trans hq⟩
    · rintro ⟨a,ha,hq⟩
      exact ⟨a,ha,(congrArg Subtype.val (congrFun hG a)).symm.trans hq⟩
  exact
    { context := C
      baseInclusion := Set.Subset.refl _
      sourceArity := P.sourceArity
      targetArity := P.targetArity
      source := gammaNativePresentation P.source (P.sourceGamma.target G P.sourceSpecial.chain) hNames
      target := gammaNativePresentation P.target (P.targetGamma.target G P.targetSpecial.chain) hNames
      sourceSpecial := TA
      targetSpecial := TB
      sourceGamma := gamma_chain_presentation_gamma P.sourceSpecial.chain P.sourceGamma hNames
      targetGamma := gamma_chain_presentation_gamma P.targetSpecial.chain P.targetGamma hNames
      sourcePullback := P.sourcePullback
      targetPullback := P.targetPullback
      forwardContractible := hForward
      backwardContractible := hBackward
      conjugateGamma := hGamma
      keyMap := contractionMap g hForward
      keyBijective := (contraction_bijective_iff g hg hForward).mpr hBackward
      keySquare := contractionMap_spec g hForward }

theorem in_fixed_context_eq (P : UniformBalancedPositionPreparation G C F hBalanced hNames) :
    P.inFixedContext.context = C := rfl

end UniformBalancedPositionPreparation
end IntegrationInACVF.Section7
