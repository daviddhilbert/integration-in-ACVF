import Integration7.GammaVolumeWitnessVFCodes
import IntegrationSection6.GammaPreparedRowAgreements

/-! Prepared RV keys retain the complete coordinate and density rows
and every supported-Jacobian comparison in a volume certificate. -/
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

def GammaVolumeParameterRecode.prepared (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) :
    GammaVolumeParameterRecode B p (p+l) (fun _ => .vf) (fun _ => .rv) :=
  ⟨GammaParameterRecode.prepared T hT⟩

theorem gamma_prepared_volume_object_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (F : GammaRVVolumeSchema B p a k (fun _ => .vf))
    (hF : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).VolumeObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).VolumeObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_object_agreement T hT F.object (fun x y hxy => (hF x y hxy).1) x,
    gamma_prepared_relation_agreement T hT ⟨F.density,F.density_definable⟩
      (fun x y hxy => (hF x y hxy).2) x⟩

theorem gamma_prepared_volume_iso_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaRVVolumeIsoSchema B p a b k (fun _ => .vf))
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).IsoAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).IsoAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.source (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.target (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_relation_agreement T hT ⟨H.chart,H.chart_definable⟩
      (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_object_agreement T hT H.exception (fun x y hxy => (hH x y hxy).2.2.2) x⟩

theorem gamma_prepared_volume_certificate_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain)
    (H : GammaRVVolumeIsoCertificateSchema B p a b k (fun _ => .vf)) (h : H.extraArity = 0)
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CertificateAgreement H h
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).CertificateAgreement H h
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  gamma_prepared_volume_iso_agreement T hT (H.withoutAuxiliary h) hH x

end IntegrationInACVF.Section7
