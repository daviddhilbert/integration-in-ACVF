module

public import Integration7.PreparedVolumeGeometryContexts
public import Integration7.VolumeGeometryVFCodesInBase
public import Integration7.VFFieldContainingVolumeContexts
public import IntegrationSection6.GammaSpecialBaseReduction
public import IntegrationSection6.GammaVFCodePreparation

@[expose] public section

/-! Prepare the geometry of finitely many common-volume certificates,
without assuming that they cover every original VF parameter. -/
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

theorem prepare_volume_geometry_in_context
    (C₀ : BaseContext M) (hBC₀ : B.real ⊆ (C₀.base : Set M))
    (A : DefSet (M := M) (C₀.base : Set M) p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B p a k (fun _ => .vf)) (G : GammaRVVolumeSchema B p b k (fun _ => .vf))
    (J : Finset (GammaVolumeCommonSchema F G)) :
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ l : ℕ, ∃ C : DefSet (M := M) (D.base : Set M) p l,
      ∃ T : SpecialBijection (SpecialTransformations.Section5.extendBase A hC₀D) C,
      ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier C) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : C, (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ W ∈ J, ∀ x : C,
        (GammaVolumeParameterRecode.prepared T hT).CommonGeometryAgreement W
          (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  let CF := vfFieldNamedBase B
  let D := vfFieldContainingVolumeContext C₀ B hBC₀
  have hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inl hx)
  have hCFD : CF.real ⊆ (D.base : Set M) :=
    fun _ hx => vfFieldContainingVolumeContext_contains C₀ B hBC₀ (Or.inr hx)
  let A' := SpecialTransformations.Section5.extendBase A hC₀D
  have hA' : GammaSetDefinable CF (carrier A') := hA.mono Set.subset_union_left (Set.Subset.refl _)
  let L : GammaFormulaBaseChange B CF := ⟨fun _ _ hd => hd.mono Set.subset_union_left (Set.Subset.refl _)⟩
  have hCode := volume_common_geometry_cover_vf_code_in_base L (vfFieldNamedBase_field B) J
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
  intro W hW x
  exact gamma_prepared_volume_common_geometry_agreement T hT W
    (fun x y hxy => (hrows x y hxy).2.2 W hW) x

end IntegrationInACVF.Section7
