import IntegrationSection6.FiniteGammaSpecialChains

/-! The actual original-Gamma special-bijection correspondence on RV[k].
The output and every intermediate RV object are finite-volume. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_6_10_gamma {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaRVFiniteObject B n) {l : ℕ}
    {C : SpecialTransformations.Section5.DefSet (M := M) U.codes n l}
    (T : SpecialBijection (typedLift U.object) C) (hΓ : GammaChainDefinable B T.chain) :
    ∃ hC : Map.FiniteFibres (rvObjectVolume (pullbackObject C)),
      @IteratedBlowup M N hN U.codes n T.length (ofGamma U) ⟨pullbackObject C,hC⟩ := by
  have h := (gammaChain_blowup_pair hκ hs h00 hsmall U.real_contains T.chain hΓ).1
    (@RVObject.domain M N U.codes n U.object) (@RVObject.volume M N U.codes n U.object)
    U.finite_volume (normalizedTypedLift_presents U.object) T.alternating
  exact h

def gammaSpecialImage {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaRVFiniteObject B n) {l : ℕ}
    {C : SpecialTransformations.Section5.DefSet (M := M) U.codes n l}
    (T : SpecialBijection (typedLift U.object) C) (hΓ : GammaChainDefinable B T.chain) :
    GammaRVFiniteObject B n where
  toGammaRVObject := gammaPullbackObject (gammaLogicInput B) U.real_contains C
    (GammaChainDefinable.target B T.chain hΓ)
  finite_volume := Classical.choose (corollary_6_10_gamma hκ hs h00 hsmall U T hΓ)

@[simp] theorem gammaSpecialImage_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (U : GammaRVFiniteObject B n) {l : ℕ}
    {C : SpecialTransformations.Section5.DefSet (M := M) U.codes n l}
    (T : SpecialBijection (typedLift U.object) C) (hΓ : GammaChainDefinable B T.chain) :
    (gammaSpecialImage hκ hs h00 hsmall U T hΓ).object = pullbackObject C := rfl

end IntegrationInACVF.Section6.FiniteRV
