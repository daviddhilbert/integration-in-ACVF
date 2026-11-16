module

public import Integration7.GammaPreparedVolumeRows
public import Integration7.FrozenVolumeWitnessRecoding

@[expose] public section

/-! Descent of primitive rows through every internal volume object,
elementary blowup and comparison in a finite common witness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b k : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
variable {U : GammaRVVolumeSchema B p a k (fun _ => .vf)}
variable {V : GammaRVVolumeSchema B p b k (fun _ => .vf)}

theorem gamma_prepared_volume_certificate_geometry_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .vf))
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CertificateGeometryAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).CertificateGeometryAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.source (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.target (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_relation_agreement T hT ⟨H.chart,H.chart_definable⟩
      (fun x y hxy => (hH x y hxy).2.2) x⟩

theorem gamma_prepared_volume_blowup_geometry_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaRVVolumeBlowupSchema U V) 
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).BlowupGeometryAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).BlowupGeometryAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.center (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.remainder (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_volume_certificate_geometry_agreement T hT H.sourceChart
      (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_volume_certificate_geometry_agreement T hT H.resultChart
      (fun x y hxy => (hH x y hxy).2.2.2) x⟩

theorem gamma_prepared_volume_chain_geometry_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) {r : ℕ} (H : GammaVolumeChainSchema U V r) :
    (∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).ChainGeometryAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val)) →
    ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).ChainGeometryAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  induction H with
  | iso H => exact gamma_prepared_volume_certificate_geometry_agreement T hT H
  | step W head tail ih =>
    intro hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT W (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_blowup_geometry_agreement T hT head (fun x y hxy => (hH x y hxy).2.1) x,
      ih (fun x y hxy => (hH x y hxy).2.2) x⟩

theorem gamma_prepared_volume_common_geometry_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaVolumeCommonSchema U V) 
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonGeometryAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).CommonGeometryAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.leftObject (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.rightObject (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_volume_chain_geometry_agreement T hT H.leftChain (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_volume_chain_geometry_agreement T hT H.rightChain (fun x y hxy => (hH x y hxy).2.2.2.1) x,
    gamma_prepared_volume_certificate_geometry_agreement T hT H.comparison
      (fun x y hxy => (hH x y hxy).2.2.2.2) x⟩

end IntegrationInACVF.Section7
