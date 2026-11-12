import IntegrationSection6.FiniteGammaPartialCharts
import IntegrationSection6.FiniteGammaLiteralCharts
import IntegrationSection6.FiniteGammaChainTransport
import IntegrationSection6.CanonicalPullbackPresentation

/-! Corollary6.10 with full original-Gamma charts on every actual RV[k]
blowup, rather than only Gamma certificates for the mixed special maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaChain_charted_pair {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S)
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l} (T : Chain S n A C) :
    ∀ hΓ : GammaChainDefinable B T,
    (∀ (V : @SpecialTransformations.DefinableGeometry.DefSet LRV M N (@rawRVSpace M N m) S)
       (v : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S V
          (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N (@rawRVSpace M N n) S))
       (hV : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S V _ v)
       (h : @PresentsLift M N hN S n (@RVObject.mk M N S n m V v) (normalizedPointSet A)),
      T.Alternating none →
      ∃ hC : Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
        GammaIteratedBlowup hκ hs h00 hsmall  T.length
          (gammaLiteralAt hBS ⟨@RVObject.mk M N S n m V v,hV⟩ h (GammaChainDefinable.source B T hΓ))
          (gammaPullbackAt hBS C (GammaChainDefinable.target B T hΓ) hC)) ∧
    (IsRVPullback (carrier A) →
      ∀ hAF : Map.FiniteFibres (rvObjectVolume (pullbackObject A)),
      T.Alternating (some true) →
      ∃ hC : Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
        GammaIteratedBlowup hκ hs h00 hsmall  T.length
          (gammaPullbackAt hBS A (GammaChainDefinable.source B T hΓ) hAF)
          (gammaPullbackAt hBS C (GammaChainDefinable.target B T hΓ) hC)) := by
  induction T with
  | nil A =>
    intro hΓ
    constructor
    · intro V v hV h _
      let U := gammaLiteralAt hBS ⟨@RVObject.mk M N S n _ V v,hV⟩ h hΓ
      let P := gammaPresentationAt U h hΓ
      exact ⟨P.object.property,.zero ⟨(gammaPresentationIsoAt U h hΓ).symm⟩⟩
    · intro _ hAF _
      exact ⟨hAF,GammaIteratedBlowup.refl _⟩
  | @cons m l k A D C p tail ih =>
    intro hΓ
    have ih := ih hΓ.2
    cases p with
    | canonical A =>
      constructor
      · intro V v hV h hT
        let U := gammaLiteralAt hBS ⟨@RVObject.mk M N S n m V v,hV⟩ h hΓ.1
        let R := gammaCanonicalAt U h hΓ.1
        have hR := normalizedPresentsLift_canonical h
        have hAlt := chainAlternating_none hT.2
        obtain ⟨hC,ht⟩ := ih.1 (@RVObject.domain M N S n R.object.obj)
          (@RVObject.volume M N S n R.object.obj) R.object.property hR hAlt
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,zero_add] using
          ht.sourceIso (gammaCanonicalIsoAt U h hΓ.1).symm⟩
      · intro hA hAF hT
        have hR := normalizedCanonicalImage_presents A hA
        let R := @pullbackObject M sM hM S n m A
        have hAlt := chainAlternating_none hT.2
        obtain ⟨hC,ht⟩ := ih.1 (@RVObject.domain M N S n R) (@RVObject.volume M N S n R) hAF hR hAlt
        have hRe : gammaLiteralAt hBS
            (⟨@RVObject.mk M N S n (n+m) (@RVObject.domain M N S n R) (@RVObject.volume M N S n R),hAF⟩ : @RVFiniteObject M N S n)
            hR (GammaChainDefinable.source B tail hΓ.2) = gammaPullbackAt hBS A hΓ.1 hAF := by
          rfl
        rw [hRe] at ht
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,zero_add] using ht⟩
    | centripetal D =>
      constructor
      · intro V v hV h hT
        let U := gammaLiteralAt hBS ⟨@RVObject.mk M N S n m V v,hV⟩ h hΓ.1.1
        let E := gammaPartialFocusBlowupAt hκ hs h00 hsmall  U h D hΓ.1.1 hΓ.1.2
        let R := gammaPartialFocusImageAt hκ hs h00 hsmall U h D hΓ.1.1 hΓ.1.2
        have hA := (pullback_normalize (carrier A)).mp
          (@PresentsLift.pullback M N hN S n U.object.obj (normalizedPointSet A) h)
        obtain ⟨hC,ht⟩ := ih.2 (D.etaImage_pullback hA) R.object.property hT.2
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,Nat.add_comm] using
          GammaIteratedBlowup.cons ⟨E⟩ ht⟩
      · intro _ _ hT
        exact False.elim (hT.1 rfl)

end IntegrationInACVF.Section6.FiniteRV
