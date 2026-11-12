import IntegrationSection6.ElementaryLiftDiagram

/-! The elementary case of6.13 on the actual released lifts, retaining
the full original-Gamma isomorphism graph. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem typedLift_carrier (U : @RVObject M N S n) :
    carrier (typedLift U) = carrier (rawLift U) := by
  ext p
  exact typedLift_mem U p

theorem elementary_lifts_isomorphic {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) {U : GammaRVObject B n} {i : Fin n}
    (hAd : GammaAdmissible U i) :
    Nonempty (GammaIso B U.lift (carrier (rawLift (@elementary M N hN U.codes n U.object i)))) := by
  obtain ⟨D⟩ := lemma_6_12 hκ hs h00 hsmall hB hAd
  exact ⟨D.liftIso.congr (typedLift_carrier U.object)
    (typedLift_carrier (@elementary M N hN U.codes n U.object i))⟩

theorem elementary_lift_gamma_definable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)
    (hB : VFGammaGeneratedBase B) {U : GammaRVObject B n} {i : Fin n}
    (hAd : GammaAdmissible U i) :
    GammaSetDefinable B (carrier (rawLift (@elementary M N hN U.codes n U.object i))) := by
  obtain ⟨e⟩ := elementary_lifts_isomorphic hκ hs h00 hsmall hB hAd
  exact e.target_definable (gammaLogicInput B)

end IntegrationInACVF.Section6
