import IntegrationSection6.FiniteRVTheorems

/-! Corollary6.10 restated on RV[k]: the special image and every
intermediate blowup are objects of the finite-volume full category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem corollary_6_10 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : @RVFiniteObject M N S n) {l : ℕ}
    {C : SpecialTransformations.Section5.DefSet (M := M) S n l}
    (T : SpecialBijection (typedLift U.obj) C) :
    ∃ V : @RVFiniteObject M N S n,
      V.obj = @pullbackObject M sM hM S n l C ∧
      @IteratedBlowup M N hN S n T.length U V := by
  have h := IntegrationInACVF.Section6.corollary_6_10 hκ hs hsmall U.obj T
  let R := @pullbackObject M sM hM S n l C
  have hsN := @Saturated.normalize M sM κ hs
  letI := N
  letI := hN
  have hR : R.volume.FiniteFibres := h.finite_volume hκ hsN hsmall U.property
  exact ⟨⟨R,hR⟩,rfl,ambientChain_toFinite hκ hsN hsmall h U.property hR⟩

end IntegrationInACVF.Section6.FiniteRV
