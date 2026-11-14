import Integration7.RVProductDimension
import Integration7.DefinableHeadCorrection
import Integration7.EssentialBlowupChart
import Section9.GenericRVJacobian
import Section9.ZeroArityVolumeJacobian

/-! Pulling the head exception through an actual blowup chart adds one
coordinate. The zero-dimensional head has its pointwise empty determinant. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.ElementaryBlowup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem head_ae_pullback {U W : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U W) {P : U.essential.obj.domain → Prop}
    (hP : RVAlmostEverywhere U.essential.obj.domain k P) :
    RVAlmostEverywhere W.essential.obj.domain (k + 1)
      (fun w => P (Map.prodFst _ _ (b.essentialChartMap w))) := by
  have hp := hP.product_right (nonzeroBlowupConeSet S)
  let F : Map W.essential.obj.domain
      (rvProductDomain U.essential.obj.domain (nonzeroBlowupConeSet S)) :=
    (rvPack U.essential.obj.domain (nonzeroBlowupConeSet S)).toImage.comp b.essentialChartMap
  have hF : Function.Injective F :=
    (rvPackToImage_bijective _ _).1.comp b.essentialChartMap_bijective.1
  apply (RVAlmostEverywhere.pullback_injective F hF hp).mono
  intro w hw
  simpa only [F, Map.comp_apply, rvUnpack_pack] using hw

theorem exists_headJacobian_after_blowup
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V WU WV : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup U WU) (c : ElementaryBlowup V WV) (f : RVVolumeIso U V) :
    ∃ J : Map U.essential.obj.domain (DefSet.univ (rawRVSpace (M := M) 1) (C.base : Set M)),
      RVAlmostEverywhere WU.essential.obj.domain (k + 1) (fun w =>
        IsRVJacobianAt
          (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
          (U.essential.obj.value (Map.prodFst _ _ (b.essentialChartMap w)) ∘ Fin.castSucc)
          (V.essential.obj.value (finiteIsoMap f.iso (Map.prodFst _ _ (b.essentialChartMap w))) ∘ Fin.castSucc)
          ((J (Map.prodFst _ _ (b.essentialChartMap w))).val 0)) := by
  cases k with
  | zero =>
    refine ⟨rvScalarOne U.essential.obj.domain, ?_⟩
    let D := DefSet.empty (rawRVSpace (M := M) WU.essential.obj.arity) (C.base : Set M)
    have hd : rvDim D = 0 := (rvDim_eq_zero_iff_finite D).mpr Set.finite_empty
    refine ⟨D, Set.empty_subset _, ?_, ?_⟩
    · rw [hd]
      decide
    · intro w _
      change IsRVJacobianAt _ _ _ 1
      apply isRVJacobianAt_zero_arity
      exact ⟨Map.prodFst _ _ (b.essentialChartMap w), rfl⟩
  | succ l =>
    obtain ⟨J, D, hD, hd, hJ⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ l)
      (blowupHeadIso C f b.admissible c.admissible)
      (fun u i => U.essential_nonzero u i.castSucc)
      (fun v i => V.essential_nonzero v i.castSucc)
    have hbase : RVAlmostEverywhere U.essential.obj.domain (l + 1) (fun u =>
        IsRVJacobianAt
          (volumeCorrespondence (finiteIsoMap (blowupHeadIso C f b.admissible c.admissible))).carrier
          (U.essential.obj.value u ∘ Fin.castSucc)
          (V.essential.obj.value (finiteIsoMap f.iso u) ∘ Fin.castSucc) ((J u).val 0)) :=
      ⟨D, hD, hd, hJ⟩
    exact ⟨J, b.head_ae_pullback hbase⟩

end IntegrationInACVF.Section7.ElementaryBlowup
