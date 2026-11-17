module

public import Integration7.GammaPreparedVolumeWitnesses
public import Integration7.GammaVolumeWitnessVFCodesInBase
public import Integration7.VFFieldContainingVolumeContexts
public import IntegrationSection6.GammaSpecialBaseReduction
public import IntegrationSection6.GammaVFCodePreparation

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! A finite cover of original-base volume witnesses is prepared in
a genuine small containing context. The internal coefficient-field names
are eliminated from the special chain and every descended witness row. -/
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

theorem gamma_prepare_volume_common_witness_cover_in_context
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset {H : GammaVolumeCommonSchema F G // H.NoAuxiliary})
    (hCover : ∀ x : A, ∃ W ∈ J, W.val.valid (rawVFParameter x.val)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ C : DefSet (M := M) (D.base : Set M) p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hC₀D) C,
      ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier C) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : C, ∃ W ∈ J,
        ((GammaVolumeParameterRecode.prepared T hT).common W.val W.property).valid (rawPreparedKey x.val) := by
  let CF := vfFieldNamedBase B
  let D := vfFieldContainingVolumeContext C₀ B hBC₀
  have hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inl hx)
  have hCFD : CF.real ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inr hx)
  let A' := SpecialTransformations.Section5.extendBase A hC₀D
  have hA' : GammaSetDefinable CF (carrier A') := hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF := ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode := gamma_volume_common_cover_vf_code_in_base L (vfFieldNamedBase_field B) J
  obtain ⟨l,C,T,hTC,hC,hrows⟩ := gamma_prepare_vf_row_code (B := CF) C₀.saturated C₀.model00
    (vfFieldNamedBase_small B C₀.uncountable ((Cardinal.mk_le_mk_of_subset hBC₀).trans_lt C₀.small))
    (vfFieldNamedBase_field B) hCFD A' hA' _ hCode
  have hT : GammaChainDefinable B T.chain := (vfFieldBaseReduction B).chainDefinable T.chain hTC
  have hF : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT F (fun x y hxy => (hrows x y hxy).1)
  have hG : ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_volume_object_agreement T hT G (fun x y hxy => (hrows x y hxy).2.1)
  refine ⟨D,hC₀D,l,C,T,hT,hC,hF,hG,?_⟩
  intro x
  obtain ⟨W,hW,hvalid⟩ := hCover ⟨(T.inverseMap x).val,(T.inverseMap x).property⟩
  have hAg := gamma_prepared_volume_common_agreement T hT W.val W.property
    (fun x y hxy => (hrows x y hxy).2.2 W hW) x
  exact ⟨W,hW,(GammaVolumeParameterRecode.prepared T hT).common_valid W.val W.property _ _
    (fun j => ((T.inverseMap x).val.1 j).property) (fun j => ((flatKey x.val).2 j).property)
    (hF x) (hG x) hAg hvalid⟩

end IntegrationInACVF.Section7
