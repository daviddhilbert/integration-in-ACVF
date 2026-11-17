module

public import Integration7.GammaPreparedVolumeWitnesses
public import Integration7.GammaVolumeWitnessVFCodesInBase
public import IntegrationSection6.GammaFieldBaseReduction
public import IntegrationSection6.GammaSpecialBaseReduction
public import IntegrationSection6.GammaVFCodePreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Prepare volume witnesses over an arbitrary small real base.
An internal generated coefficient field codes the unchanged formulas;
the resulting special chain is proved definable over the original base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

theorem gamma_prepare_volume_common_witness_cover_without_field {κ : Cardinal}
    (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset {H : GammaVolumeCommonSchema F G // H.NoAuxiliary})
    (hCover : ∀ x : A, ∃ W ∈ J, W.val.valid (rawVFParameter x.val)) :
    ∃ R : Set M, ∃ hSR : S ⊆ R, ∃ hBR : B.real ⊆ R, ∃ l : ℕ, ∃ C : DefSet (M := M) R p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hSR) C,
      ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier C) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : C, ∃ W ∈ J,
        ((GammaVolumeParameterRecode.prepared T hT).common W.val W.property).valid (rawPreparedKey x.val) := by
  let CF := vfFieldNamedBase B
  let R := S ∪ CF.real
  have hSR : S ⊆ R := Set.subset_union_left
  let A' := SpecialTransformations.Section5.extendBase A hSR
  have hA' : GammaSetDefinable CF (carrier A') := hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF := ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode := gamma_volume_common_cover_vf_code_in_base L (vfFieldNamedBase_field B) J
  obtain ⟨l,C,T,hTC,hC,hrows⟩ := gamma_prepare_vf_row_code (B := CF) hs h00
    (vfFieldNamedBase_small B hκ hsmall) (vfFieldNamedBase_field B) Set.subset_union_right A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain := (vfFieldBaseReduction B).chainDefinable T.chain hTC
  have hF : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT F (fun x y hxy => (hrows x y hxy).1)
  have hG : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT G (fun x y hxy => (hrows x y hxy).2.1)
  refine ⟨R,hSR,(fun c hc => Or.inr (Or.inl hc)),l,C,T,hT,hC,hF,hG,?_⟩
  intro x
  obtain ⟨W,hW,hvalid⟩ := hCover ⟨(T.inverseMap x).val,(T.inverseMap x).property⟩
  have hAg := gamma_prepared_volume_common_agreement T hT W.val W.property
    (fun x y hxy => (hrows x y hxy).2.2 W hW) x
  exact ⟨W,hW,(GammaVolumeParameterRecode.prepared T hT).common_valid W.val W.property _ _
    (fun j => ((T.inverseMap x).val.1 j).property) (fun j => ((flatKey x.val).2 j).property)
    (hF x) (hG x) hAg hvalid⟩

end IntegrationInACVF.Section7
