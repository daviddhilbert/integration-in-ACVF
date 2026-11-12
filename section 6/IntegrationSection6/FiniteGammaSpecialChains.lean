import IntegrationSection6.FiniteGammaPartialFocus
import IntegrationSection6.FiniteRVChainTransport
import IntegrationSection6.CanonicalPullbackPresentation
import IntegrationSection6.NormalizedCanonicalLifts

/-! Corollary6.10 over the original Gamma base, entirely in RV[k].
No internal code set is bounded by the saturation cardinal. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem gammaChain_blowup_pair {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S)
    {m l : ℕ} {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l} (T : Chain S n A C) :
    GammaChainDefinable B T →
    (∀ (V : @SpecialTransformations.DefinableGeometry.DefSet LRV M N
          (@SpecialTransformations.Section4.rawRVSpace M N m) S)
       (v : @SpecialTransformations.DefinableGeometry.Map LRV M N _ _ S V
          (@SpecialTransformations.DefinableGeometry.DefSet.univ LRV M N
            (@SpecialTransformations.Section4.rawRVSpace M N n) S))
       (hV : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M N _ _ S V _ v),
      @PresentsLift M N hN S n (@RVObject.mk M N S n m V v) (normalizedPointSet A) →
      T.Alternating none →
      ∃ hC : Map.FiniteFibres (rvObjectVolume (@pullbackObject M sM hM S n l C)),
        @IteratedBlowup M N hN S n T.length ⟨@RVObject.mk M N S n m V v,hV⟩
          ⟨@pullbackObject M sM hM S n l C,hC⟩) ∧
    (IsRVPullback (carrier A) →
      ∀ hAF : Map.FiniteFibres (rvObjectVolume (@pullbackObject M sM hM S n m A)),
      T.Alternating (some true) →
      ∃ hC : Map.FiniteFibres (rvObjectVolume (@pullbackObject M sM hM S n l C)),
        @IteratedBlowup M N hN S n T.length
          ⟨@pullbackObject M sM hM S n m A,hAF⟩
          ⟨@pullbackObject M sM hM S n l C,hC⟩) := by
  induction T with
  | nil A =>
    intro hΓ
    constructor
    · intro V v hV h _
      let e := pullbackPresentationIso h
      letI := N
      letI := hN
      have hC := (finite_volume_iso e).mpr hV
      exact ⟨hC,.zero ⟨rvFiniteIsoOfAmbient e.symm⟩⟩
    · intro _ hA _
      letI := N
      letI := hN
      exact ⟨hA,.zero ⟨Iso.refl _⟩⟩
  | @cons m l k A B C p tail ih =>
    intro hΓ
    have ih := ih hΓ.2
    cases p with
    | canonical A =>
      constructor
      · intro V v hV h hT
        let U := @RVObject.mk M N S n m V v
        have hR := normalizedPresentsLift_canonical h
        let R := @canonicalRVKeyObject M N S n U
        let e := @canonicalRVKeyIso M N hN S n U
        have hAlt := chainAlternating_none hT.2
        have hRF := (@finite_volume_iso M N hN S n U R e).mp hV
        obtain ⟨hC,ht⟩ := ih.1 (@RVObject.domain M N S n R) (@RVObject.volume M N S n R) hRF hR hAlt
        letI := N
        letI := hN
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,zero_add] using
          ht.sourceIso (rvFiniteIsoOfAmbient e)⟩
      · intro hA hAF hT
        have hR := normalizedCanonicalImage_presents A hA
        let R := @pullbackObject M sM hM S n m A
        have hAlt := chainAlternating_none hT.2
        obtain ⟨hC,ht⟩ := ih.1 (@RVObject.domain M N S n R) (@RVObject.volume M N S n R) hAF hR hAlt
        have hRe : (⟨@RVObject.mk M N S n (n+m) (@RVObject.domain M N S n R)
            (@RVObject.volume M N S n R),hAF⟩ : @RVFiniteObject M N S n) = ⟨R,hAF⟩ := rfl
        rw [hRe] at ht
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,zero_add] using ht⟩
    | centripetal D =>
      constructor
      · intro V v hV h hT
        let U : @RVFiniteObject M N S n := ⟨@RVObject.mk M N S n m V v,hV⟩
        let E := gammaPartialFocusStep hκ hs h00 hsmall hBS U h D hΓ.1.1 hΓ.1.2
        have hA := (pullback_normalize (carrier A)).mp
          (@PresentsLift.pullback M N hN S n U.obj (normalizedPointSet A) h)
        obtain ⟨hC,ht⟩ := ih.2 (D.etaImage_pullback hA) E.target_finite hT.2
        let hE := E.blowup
        letI := N
        letI := hN
        exact ⟨hC,by simpa only [Chain.length,Primitive.length,Nat.add_comm,originalFocusObject] using
          IteratedBlowup.cons hE ht⟩
      · intro _ _ hT
        exact False.elim (hT.1 rfl)

end IntegrationInACVF.Section6.FiniteRV
