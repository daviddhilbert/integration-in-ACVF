import IntegrationSection6.GammaElementaryFocus
import IntegrationSection6.OriginalAdmissibleFocus
import IntegrationSection6.VolumePreservingElementary

/-! The actual original-Gamma full focus has the required elementary RV
image, after dropping preparatory canonical labels. Only B.real is small. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem GammaAdmissible.exists_original_focus_elementary {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    {U : GammaRVObject B n} {i : Fin n} (hAd : GammaAdmissible U i) :
    ∃ D : Focus (canonicalTypedLift U.object) i (Fin.castAdd (rvObjectArity U.object) i),
      D.locus = carrier (canonicalTypedLift U.object) ∧ GammaFocusDefinable B D ∧
      Nonempty (@ElementaryBlowup M N hN U.codes n U.object (originalFocusObject D)) := by
  let S0 := U.codes
  let R := U.object
  let RC := @canonicalRVKeyObject M N S0 n R
  let A := canonicalTypedLift R
  let P := @normalizedCanonicalTypedLift_presents M sM hM S0 n R
  have hAd0 := hAd.ordinary hκ hs h00 hsmall
  have hAdC := @canonicalRVKey_admissible M N hN S0 n R i hAd0
  obtain ⟨D,hD,hΓD⟩ := hAd.exists_canonical_fullFocus hκ hs h00 hsmall hB
  have hfull : carrier A ⊆ D.locus := by rw [hD]
  let E := @originalAdmissibleFocusBlowup M sM hM S0 n RC A P i
    (Fin.castAdd (rvObjectArity R) i) D hfull hAdC
  let e := @canonicalElementaryIso M N hN S0 n R i
  have hE : Nonempty (@ElementaryBlowup M N hN S0 n R (originalFocusObject D)) := by
    letI := N
    letI := hN
    exact ⟨@ElementaryBlowup.mk M N hN S0 n R
      (@originalFocusObject M sM hM S0 n (n+@rvObjectArity M sM S0 n R) A i
        (Fin.castAdd (@rvObjectArity M sM S0 n R) i) D)
      i hAd0 (E.iso.trans e)⟩
  exact ⟨D,hD,hΓD,hE⟩

end IntegrationInACVF.Section6
