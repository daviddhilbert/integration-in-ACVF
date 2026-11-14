import Integration7.GammaPreparedVolumeRows

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

theorem gamma_prepared_volume_blowup_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaRVVolumeBlowupSchema U V) (h : H.NoAuxiliary)
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement H h
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).BlowupAgreement H h
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.center (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.remainder (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_volume_certificate_agreement T hT H.sourceChart h.1
      (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_volume_certificate_agreement T hT H.resultChart h.2
      (fun x y hxy => (hH x y hxy).2.2.2) x⟩

theorem gamma_prepared_volume_chain_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) {r : ℕ} (H : GammaVolumeChainSchema U V r) :
    ∀ h : H.NoAuxiliary, (∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).ChainAgreement H h
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val)) →
    ∀ x : C, (GammaVolumeParameterRecode.prepared T hT).ChainAgreement H h
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  induction H with
  | iso H => exact fun h => gamma_prepared_volume_certificate_agreement T hT H h
  | step W head tail ih =>
    intro h hH x
    exact ⟨gamma_prepared_volume_object_agreement T hT W (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_volume_blowup_agreement T hT head h.1 (fun x y hxy => (hH x y hxy).2.1) x,
      ih h.2 (fun x y hxy => (hH x y hxy).2.2) x⟩

theorem gamma_prepared_volume_common_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaVolumeCommonSchema U V) (h : H.NoAuxiliary)
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaVolumeParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H h
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaVolumeParameterRecode.prepared T hT).CommonAgreement H h
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_volume_object_agreement T hT H.leftObject (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_volume_object_agreement T hT H.rightObject (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_volume_chain_agreement T hT H.leftChain h.1 (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_volume_chain_agreement T hT H.rightChain h.2.1 (fun x y hxy => (hH x y hxy).2.2.2.1) x,
    gamma_prepared_volume_certificate_agreement T hT H.comparison h.2.2
      (fun x y hxy => (hH x y hxy).2.2.2.2) x⟩

end IntegrationInACVF.Section7
