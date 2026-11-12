import IntegrationSection6.OriginalFocusCoordinates
import IntegrationSection6.NormalizedCanonicalLifts

/-! The elementary image of a canonical-full-focus-canonical chain and
its global, real-definable RV coordinate formula. -/
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

variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (n+@rvObjectArity M sM S n U)} (D : Focus (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) i k)
variable (hfull : carrier (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) ⊆ D.locus) (hAd : @Admissible M (@CanonicalStructure.normalize M sM) S n U i)

def canonicalFocusBlowupIso :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@originalFocusObject M sM hM S n (n+@rvObjectArity M sM S n U) (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) i k D) ≅ elementary U i :=
  let P := @normalizedPresentsLift_canonical M sM hM S n U A h
  let hC := @canonicalRVKey_admissible M N hN S n U i hAd
  let E := @originalAdmissibleFocusBlowup M sM hM S n (@canonicalRVKeyObject M N S n U)
    (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) P i k D hfull hC
  letI : LRV.Structure M := N
  letI : M ⊨ Axioms.ACVF := hN
  E.iso.trans (canonicalElementaryIso U i)

theorem canonicalFocusBlowupIso_volume (a : rvObjectDomain (originalFocusObject D)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (elementary U i).value ((@canonicalFocusBlowupIso M sM hM S n U A h i k D hfull hAd).hom.map a) =
      (@originalFocusObject M sM hM S n (n+@rvObjectArity M sM S n U) (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) i k D).value a := by
  let P := @normalizedPresentsLift_canonical M sM hM S n U A h
  let hC := @canonicalRVKey_admissible M N hN S n U i hAd
  let E := @originalAdmissibleFocusBlowup M sM hM S n (@canonicalRVKeyObject M N S n U)
    (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) P i k D hfull hC
  letI := N
  letI := hN
  exact (canonicalElementaryIso_volume U i (E.iso.hom.map a)).trans
    (@originalAdmissibleFocusBlowup_volume M sM hM S n (@canonicalRVKeyObject M N S n U)
      (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) P i k D hfull hC a)

theorem canonicalFocusBlowupIso_formula (a : rvObjectDomain (originalFocusObject D)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    ((@canonicalFocusBlowupIso M sM hM S n U A h i k D hfull hAd).hom.map a).val =
      rvAppend (fun j => a.val (Fin.natAdd n (Fin.natAdd n j)))
        (fun _ : Fin 1 => a.val (Fin.castAdd (n+@rvObjectArity M sM S n U) i) /
          a.val (Fin.natAdd n (Fin.castAdd (@rvObjectArity M sM S n U) i))) := by
  let P := @normalizedPresentsLift_canonical M sM hM S n U A h
  let hC := @canonicalRVKey_admissible M N hN S n U i hAd
  let E := @originalAdmissibleFocusBlowup M sM hM S n (@canonicalRVKeyObject M N S n U)
    (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) P i k D hfull hC
  have hk := @originalAdmissibleFocusBlowup_key M sM hM S n (@canonicalRVKeyObject M N S n U)
    (@canonicalImage M sM hM n (@rvObjectArity M sM S n U) S A) P i k D hfull hC a
  letI := N
  letI := hN
  let b := E.iso.hom.map a
  have hl : (elementaryProjection (canonicalRVKeyObject U) i b).val =
      fun j => a.val (Fin.natAdd n j) := by
    funext j
    exact (Fin.append_right _ _ j).symm.trans (congrFun hk (Fin.natAdd n j))
  have hv : (elementary (canonicalRVKeyObject U) i).value b i =
      a.val (Fin.castAdd (n+U.arity) i) := by
    exact (Fin.append_left _ _ i).symm.trans (congrFun hk (Fin.castAdd (n+U.arity) i))
  have hs : (elementaryParameter (canonicalRVKeyObject U) i b).val 0 =
      a.val (Fin.castAdd (n+U.arity) i) / a.val (Fin.natAdd n (Fin.castAdd U.arity i)) := by
    have hn := hC.rv_nonzero (elementaryProjection (canonicalRVKeyObject U) i b)
    have hd : (canonicalRVKeyObject U).value (elementaryProjection (canonicalRVKeyObject U) i b) i =
        a.val (Fin.natAdd n (Fin.castAdd U.arity i)) := congrFun hl (Fin.castAdd U.arity i)
    rw [elementary_value,blowupValue_same] at hv
    rw [← hd]
    exact (eq_div_iff hn).mpr hv
  change ((canonicalElementaryIso U i).hom.map b).val = _
  rw [canonicalElementaryIso_labels,hl]
  apply congrArg₂ rvAppend rfl
  funext j
  fin_cases j
  exact hs

end IntegrationInACVF.Section6
