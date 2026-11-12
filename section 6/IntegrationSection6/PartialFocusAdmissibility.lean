import IntegrationSection6.PartialFocusLocus

/-! The active old-label image of a partial focus is an actual admissible
RV subobject. This is the local elementary piece for the general chain proof. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Milestone0.Transfer
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (@rvObjectArity M sM S n U)} (D : Focus A i k)

def focusActiveRVObject : @RVObject M N S n :=
  @RVObject.restrict M N S n U (liftLabelLocus (focusActiveSet D))
    (liftLabelLocus_subset h (focusActiveSet_subset D))

theorem focusActiveRVObject_presents :
    @PresentsLift M N hN S n (@focusActiveRVObject M sM hM S n U A h i k D) (normalizedPointSet (focusActiveSet D)) :=
  normalizedPresentsLift_sublocus h (focusActiveSet_subset D)
    (focusActiveSet_pullback D ((pullback_normalize (carrier A)).mp (@PresentsLift.pullback M N hN S n U (normalizedPointSet A) h)))

theorem focusActiveRVObject_admissible {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    @Admissible M N S n (@focusActiveRVObject M sM hM S n U A h i k D) i := by
  let C := focusActiveSet D
  let F := activeFocus D
  let R := focusActiveRVObject h D
  have hP := focusActiveRVObject_presents h D
  have hfull := activeFocus_full D
  have hn (p : Point (M := M) n (@rvObjectArity M sM S n U))
      (hp : p ∈ carrier C) : p.1 i ≠ @Zero.zero (@VF M N) (@vfInstZero M N hN) := by
    rw [vfZero_normalize]
    exact activeFocus_field_nonzero D p hp
  let FN := normalizedFocus F
  letI := N
  letI := hN
  exact admissible_of_fullFocus hκ (@Saturated.normalize M sM κ hs) hsmall hP FN hfull hn

def partialFocusElementaryPiece {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    @ElementaryBlowup M N hN S n (@focusActiveRVObject M sM hM S n U A h i k D) (originalFocusObject (activeFocus D)) :=
  originalAdmissibleFocusBlowup (focusActiveRVObject_presents h D) (activeFocus D)
    (activeFocus_full D) (focusActiveRVObject_admissible h D hκ hs hsmall)

end IntegrationInACVF.Section6
