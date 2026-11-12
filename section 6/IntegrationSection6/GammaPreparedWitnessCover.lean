import IntegrationSection6.GammaPreparedWitnessAgreements
import IntegrationSection6.GammaVFCodePreparation
import IntegrationSection6.GammaWitnessVFCodes
import IntegrationSection6.GammaRecodingValidity

/-! A finite common-blowup witness cover over a pure VF base becomes a
valid finite cover on prepared RV keys. Validity descends by exact primitive
rows, not by assuming definability of the geometric Isp relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a b k : ℕ}

theorem gamma_prepare_common_witness_cover {κ : Cardinal} (hs : Saturated M κ)
    (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (FBase : VFFieldBase B.real) (hBS : B.real ⊆ S)
    (A : DefSet (M := M) S p 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B p a k (fun _ => .vf)) (G : GammaFiniteRVSchema B p b k (fun _ => .vf))
    (J : Finset (GammaFiniteCommonSchema F G))
    (hCover : ∀ x : A, ∃ W ∈ J, W.valid (rawVFParameter x.val)) :
    ∃ l : ℕ, ∃ C : DefSet (M := M) S p l, ∃ T : SpecialBijection A C,
      ∃ hT : GammaChainDefinable B T.chain, IsRVPullback (carrier C) ∧
      (∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement F
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      (∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement G
        (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val)) ∧
      ∀ x : C, ∃ W ∈ J, ((GammaParameterRecode.prepared T hT).common W).valid (rawPreparedKey x.val) := by
  obtain ⟨l,C,T,hT,hC,hrows⟩ := gamma_prepare_vf_row_code hs h00 hsmall FBase hBS A hA _
    (gamma_common_cover_vf_code FBase J)
  have hF : ∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement F
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_object_agreement T hT F (fun x y hxy => (hrows x y hxy).1)
  have hG : ∀ x : C, (GammaParameterRecode.prepared T hT).ObjectAgreement G
      (rawVFParameter (T.inverseMap x).val) (rawPreparedKey x.val) :=
    gamma_prepared_object_agreement T hT G (fun x y hxy => (hrows x y hxy).2.1)
  refine ⟨l,C,T,hT,hC,hF,hG,?_⟩
  intro x
  obtain ⟨W,hW,hvalid⟩ := hCover (T.inverseMap x)
  have hAg := gamma_prepared_common_agreement T hT W (fun x y hxy => (hrows x y hxy).2.2 W hW) x
  refine ⟨W,hW,?_⟩
  exact (GammaParameterRecode.prepared T hT).common_valid W _ _
    (fun j => ((T.inverseMap x).val.1 j).property) (fun j => ((flatKey x.val).2 j).property)
    (hF x) (hG x) hAg hvalid

end IntegrationInACVF.Section6
