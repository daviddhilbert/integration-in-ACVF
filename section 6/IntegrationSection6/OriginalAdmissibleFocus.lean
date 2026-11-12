import IntegrationSection6.OriginalFocusObjects
import IntegrationSection6.AdmissibleFocusRelabeling

/-! The original-model focus yields an actual elementary blowup over its
released RV presentation. Admissibility is supplied by Definition6.1;
there is no smallness hypothesis on the presentation code set. -/
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

def originalAdmissibleFocusBlowup
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U
      (@normalizedPointSet M sM hM S n (rvObjectArity U) A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i) :
    @ElementaryBlowup M N hN S n U (originalFocusObject D) := by
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
  let e3 := admissibleFullFocusBlowup h DN hfullN hAd
  exact @ElementaryBlowup.mk M N hN S n U
    (@originalFocusObject M sM hM S n (@rvObjectArity M sM S n U) A i k D)
    i hAd (e1.trans (e2.trans e3.iso))

end IntegrationInACVF.Section6
