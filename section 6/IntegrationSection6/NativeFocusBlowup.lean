import IntegrationSection6.NativeFocusObject
import Section3.NormalizationSaturation

/-! Lemma6.9 for the released post-focus RV object, rather than a newly
chosen presentation. All local instances below are the explicit normalized
model; they add no model, saturation or algebraicity assumption. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section4.rawRVSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def nativeFocusKeyIso
    {U : @RVObject M N S n}
    {A : @SpecialTransformations.Section5.DefSet M N hN S n (@rvObjectArity M sM S n U)}
    (h : @PresentsLift M N hN S n U A) {i : Fin n} {k : Fin (@rvObjectArity M sM S n U)}
    (D : @Focus M N hN S n (@rvObjectArity M sM S n U) A i k)
    (hfull : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN; carrier A ⊆ D.locus)
    (hnz : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ u : U.domain, U.value u i ≠ 0) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@nativeFocusObject M sM hM S n (@rvObjectArity M sM S n U) A i k D) ≅
      (@fullFocusObject M N hN S n U A h i k D hfull hnz) := by
  letI := N
  letI := hN
  let V := @nativeFocusObject M sM hM S n (@RVObject.arity M N S n U) A i k D
  let W := @fullFocusObject M N hN S n U A h i k D hfull hnz
  have hc : V.domain.carrier = W.domain.carrier := by
    ext r
    exact @nativeFocusObject_mem M sM hM S n (@RVObject.arity M N S n U) A i k D r
  exact rvIsoOfCarrierEq V.domain W.domain V.volume W.volume hc (fun _ => rfl)

/-- The native canonical lift, full focus, and canonical RV projection
produce an actual elementary blowup, over the original small real base. -/
def canonical_lift_fullFocus_blowup {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (U : @RVObject M N S n) {i : Fin n} {k : Fin (@rvObjectArity M sM S n U)}
    (D : @Focus M N hN S n (@rvObjectArity M sM S n U) (@normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) (@typedLift M sM hM S n U)) i k)
    (hfull : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      carrier (@normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) (@typedLift M sM hM S n U)) ⊆ D.locus)
    (hnz : letI : LRV.Structure M := N; letI : M ⊨ Axioms.ACVF := hN;
      ∀ u : U.domain, U.value u i ≠ 0) :
    @ElementaryBlowup M N hN S n U
      (@nativeFocusObject M sM hM S n (@rvObjectArity M sM S n U)
        (@normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) (@typedLift M sM hM S n U)) i k D) := by
  letI := N
  letI := hN
  let P := @normalizedTypedLift_presents M sM hM S n U
  let E := @lemma_6_9 M N hN S n U (@normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) (@typedLift M sM hM S n U)) P i k D hfull hnz
    κ hκ (@Saturated.normalize M sM κ hs) hsmall
  exact @ElementaryBlowup.mk M N hN S n U _ i E.admissible
    ((@nativeFocusKeyIso M sM hM S n U (@normalizedPointSet M sM hM S n (@rvObjectArity M sM S n U) (@typedLift M sM hM S n U)) P i k D hfull hnz).trans E.iso)

end IntegrationInACVF.Section6
