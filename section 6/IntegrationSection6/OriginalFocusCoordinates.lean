import IntegrationSection6.OriginalFocusVolume
import IntegrationSection6.KeyInverseCoordinates
import IntegrationSection6.RVFocusProgram

/-! The original-model focus relabeling has the stated RV coordinate
formula, before and after removal of preparatory canonical labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem originalAdmissibleFocusBlowup_key
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i)
    (a : rvObjectDomain (originalFocusObject D)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    let b := (@originalAdmissibleFocusBlowup M sM hM S n U A h i k D hfull hAd).iso.hom.map a
    SpecialTransformations.Section4.rvAppend ((elementary U i).value b)
      (elementaryProjection U i b).val = a.val := by
  let A' := @normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) A
  let DN := @normalizedFocus M sM hM S n (@rvObjectArity M sM S n U) A i k D
  let e1 := @originalNativeFocusIso M sM hM S n (@rvObjectArity M sM S n U) A i k D
  have hfullN :
      letI : LRV.Structure M := N
      letI : M ⊨ Axioms.ACVF := hN
      carrier A' ⊆ DN.locus := hfull
  letI := N
  letI := hN
  let e2 := @nativeFocusKeyIso M sM hM S n U A' h i k DN hfullN hAd.rv_nonzero
  let e3 := fullFocusObjectKeyIso h DN hfullN hAd.rv_nonzero
  exact elementaryKeyIso_inv_key U i hAd (e3.hom.map (e2.hom.map (e1.hom.map a)))

end IntegrationInACVF.Section6
