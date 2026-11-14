import Integration7.GammaPreparedVolumeWitnesses
import IntegrationSection6.GammaVFCodePreparation

/-! A finite cover by genuine volume witnesses over VF parameters
descends to valid witnesses on prepared RV keys. -/
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

theorem gamma_prepare_volume_common_witness_cover {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset {H : GammaVolumeCommonSchema F G // H.NoAuxiliary})
    (hCover : ∀ x : A, ∃ W ∈ J, W.val.valid (rawVFParameter x.val)) :
    ∃ l : ℕ, ∃ C : DefSet (M := M) S p l, ∃ T : SpecialBijection A C,
      ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier C) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : C, ∃ W ∈ J,
        ((GammaVolumeParameterRecode.prepared T hT).common W.val W.property).valid (rawPreparedKey x.val) := by
  obtain ⟨l,C,T,hT,hC,hrows⟩ := gamma_prepare_vf_row_code hs h00 hsmall FBase hBS A hA _
    (gamma_volume_common_cover_vf_code FBase J)
  have hF : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT F (fun x y hxy => (hrows x y hxy).1)
  have hG : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT G (fun x y hxy => (hrows x y hxy).2.1)
  refine ⟨l,C,T,hT,hC,hF,hG,?_⟩
  intro x
  obtain ⟨W,hW,hvalid⟩ := hCover (T.inverseMap x)
  have hAg := gamma_prepared_volume_common_agreement T hT W.val W.property
    (fun x y hxy => (hrows x y hxy).2.2 W hW) x
  exact ⟨W,hW,(GammaVolumeParameterRecode.prepared T hT).common_valid W.val W.property _ _
    (fun j => ((T.inverseMap x).val.1 j).property) (fun j => ((flatKey x.val).2 j).property)
    (hF x) (hG x) hAg hvalid⟩

end IntegrationInACVF.Section7
