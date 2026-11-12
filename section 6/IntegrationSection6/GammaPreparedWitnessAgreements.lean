import IntegrationSection6.GammaPreparedRowAgreements

/-! Exact primitive-row descent extends through every internal object and
chart of finite elementary blowups, chains and common-blowup witnesses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p l a b k : ℕ}
variable {A : DefSet (M := M) S p 0} {C : DefSet (M := M) S p l}
variable {U : GammaFiniteRVSchema B p a k (fun _ => .vf)}
variable {V : GammaFiniteRVSchema B p b k (fun _ => .vf)}

theorem gamma_prepared_blowup_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaFiniteBlowupSchema U V)
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).BlowupAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).BlowupAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_object_agreement T hT H.center (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_object_agreement T hT H.remainder (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_iso_agreement T hT H.sourceChart (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_iso_agreement T hT H.resultChart (fun x y hxy => (hH x y hxy).2.2.2) x⟩

theorem gamma_prepared_chain_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) {r : ℕ} (H : GammaFiniteChainSchema U V r) :
    (∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).ChainAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val)) →
    ∀ x : C, (GammaParameterRecode.prepared T hT).ChainAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) := by
  induction H with
  | iso H => exact gamma_prepared_iso_agreement T hT H
  | step W head tail ih =>
    intro hH x
    exact ⟨gamma_prepared_object_agreement T hT W (fun x y hxy => (hH x y hxy).1) x,
      gamma_prepared_blowup_agreement T hT head (fun x y hxy => (hH x y hxy).2.1) x,
      ih (fun x y hxy => (hH x y hxy).2.2) x⟩

theorem gamma_prepared_common_agreement (T : SpecialBijection A C)
    (hT : GammaChainDefinable B T.chain) (H : GammaFiniteCommonSchema U V)
    (hH : ∀ x y : C, SameRV x.val y.val →
      (GammaParameterRecode.identity B p (fun _ => .vf)).CommonAgreement H
        (rawVFParameter (T.inverseMap x).val) (rawVFParameter (T.inverseMap y).val))
    (x : C) : (GammaParameterRecode.prepared T hT).CommonAgreement H
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
  ⟨gamma_prepared_object_agreement T hT H.leftObject (fun x y hxy => (hH x y hxy).1) x,
    gamma_prepared_object_agreement T hT H.rightObject (fun x y hxy => (hH x y hxy).2.1) x,
    gamma_prepared_chain_agreement T hT H.leftChain (fun x y hxy => (hH x y hxy).2.2.1) x,
    gamma_prepared_chain_agreement T hT H.rightChain (fun x y hxy => (hH x y hxy).2.2.2.1) x,
    gamma_prepared_iso_agreement T hT H.comparison (fun x y hxy => (hH x y hxy).2.2.2.2) x⟩

end IntegrationInACVF.Section6
