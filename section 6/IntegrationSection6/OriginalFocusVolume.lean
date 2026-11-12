import IntegrationSection6.OriginalAdmissibleFocus

/-! The original-model focus comparison preserves every volume coordinate.
Its lift therefore gives the actual VF-identity relabeling without a bound
on the internal presentation code set. -/
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

theorem originalAdmissibleFocusBlowup_volume
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i)
    (a : rvObjectDomain (originalFocusObject D)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (elementary U i).value
      ((@originalAdmissibleFocusBlowup M sM hM S n U A h i k D hfull hAd).iso.hom.map a) =
      (@originalFocusObject M sM hM S n (@rvObjectArity M sM S n U) A i k D).value a := by
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
  let p := e2.hom.map (e1.hom.map a)
  change (elementary U i).value ((admissibleFullFocusBlowup h DN hfullN hAd).iso.hom.map p) = _
  exact admissibleFullFocusBlowup_volume h DN hfullN hAd p

def originalFocusRelabelLift
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i) :=
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  @volumePreservingLiftMap M N hN S n
    (@originalFocusObject M sM hM S n (@rvObjectArity M sM S n U) A i k D)
    (@elementary M N hN S n U i)
    (@originalAdmissibleFocusBlowup M sM hM S n U A h i k D hfull hAd).iso.hom.map
    (@originalAdmissibleFocusBlowup_volume M sM hM S n U A h i k D hfull hAd)

theorem originalFocusRelabelLift_bijective
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i) :
    Function.Bijective (originalFocusRelabelLift h D hfull hAd) := by
  letI := N
  letI := hN
  exact @volumePreservingLiftMap_bijective M N hN S n
    (@originalFocusObject M sM hM S n (@rvObjectArity M sM S n U) A i k D)
    (@elementary M N hN S n U i)
    (@originalAdmissibleFocusBlowup M sM hM S n U A h i k D hfull hAd).iso.hom.map
    (@originalAdmissibleFocusBlowup_volume M sM hM S n U A h i k D hfull hAd)
    (iso_map_bijective (@originalAdmissibleFocusBlowup M sM hM S n U A h i k D hfull hAd).iso)

@[simp] theorem originalFocusRelabelLift_vf
    {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    {i : Fin n} {k : Fin (rvObjectArity U)} (D : Focus A i k)
    (hfull : carrier A ⊆ D.locus) (hAd : @Admissible M N S n U i)
    (a : rawLift (originalFocusObject D)) :
    (originalFocusRelabelLift h D hfull hAd a).val.1 = a.val.1 := rfl

end IntegrationInACVF.Section6
