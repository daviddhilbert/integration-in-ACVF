import IntegrationSection6.PartialFocusPartition
import IntegrationSection6.PartialFocusAdmissibility
import IntegrationSection6.LiftComplement
import IntegrationSection6.BlowupPresentations

/-! A partial centripetal transformation is one genuine blowup: replace
the admissible active old-label locus and retain its RV complement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
variable {U : @RVObject M (@CanonicalStructure.normalize M sM) S n}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable {i : Fin n} {k : Fin (@rvObjectArity M sM S n U)} (D : Focus A i k)

def partialFocusBlowup {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    @Blowup M N hN S n U (originalFocusObject D) := by
  have hA := (pullback_normalize (carrier A)).mp
    (@PresentsLift.pullback M N hN S n U (normalizedPointSet A) h)
  let C := focusActiveSet D
  let E := focusInactiveSet D
  let R := focusActiveRVObject h D
  let L := liftLabelLocus C
  have hc := liftLabelLocus_subset h (focusActiveSet_subset D)
  have hCP := focusActiveSet_pullback D hA
  have hEP := focusInactiveSet_pullback D hA
  have hp := partialFocus_source_partition D
  have hd : Disjoint (carrier C) (carrier E) := by
    apply Set.disjoint_left.mpr
    intro p hc he
    exact he.2 hc
  let eC := partialFocusElementaryPiece h D hκ hs hsmall
  let eE := liftComplementIso h hp hd hCP hEP
  let eT := partialFocusRVSplit D hA
  letI := N
  letI := hN
  let Q := U.restrict (complement U L) (complement_subset U L)
  let es : U ≅ rvCoprodObject R Q := (partitionIso U L hc).symm
  let et := eT.trans (rvCoprodIso eC.iso eE)
  exact Blowup.of_split i (@focusActiveRVObject_admissible M sM hM S n U A h i k D κ hκ hs hsmall) es et

end IntegrationInACVF.Section6
