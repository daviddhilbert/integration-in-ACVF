import IntegrationSection6.LiftLabelPartitions
import IntegrationSection6.LiftRVImage
import IntegrationSection6.Subobjects

/-! The unchanged member of a lift partition recovers exactly the RV
complement of the active old-label locus, with an actual definable isomorphism. -/
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
variable {A C E : SpecialTransformations.Section5.DefSet (M := M) S n (@rvObjectArity M sM S n U)}
variable (h : @PresentsLift M (@CanonicalStructure.normalize M sM) (@CanonicalStructure.normalized_model M sM hM) S n U (normalizedPointSet A))
variable (hpart : carrier A = carrier C ∪ carrier E)
variable (hCE : Disjoint (carrier C) (carrier E)) (hC : IsRVPullback (carrier C))

include h hpart hCE hC in
theorem liftLabelLoci_complement : carrier (liftLabelLocus E) =
    carrier (rvObjectDomain U) \ carrier (liftLabelLocus C) := by
  have hCA : carrier C ⊆ carrier A := fun p hp => (Set.ext_iff.mp hpart p).mpr (Or.inl hp)
  have hEA : carrier E ⊆ carrier A := fun p hp => (Set.ext_iff.mp hpart p).mpr (Or.inr hp)
  have hcover := liftLabelLoci_cover h hpart
  have hdisj := liftLabelLoci_disjoint h hCA hEA hCE hC
  ext r
  constructor
  · intro hr
    exact ⟨(Set.ext_iff.mp hcover r).mpr (Or.inr hr),fun hc => Set.disjoint_left.mp hdisj hc hr⟩
  · rintro ⟨hr,hn⟩
    rcases (Set.ext_iff.mp hcover r).mp hr with hc | he
    · exact False.elim (hn hc)
    · exact he

def liftComplementIso (hE : IsRVPullback (carrier E)) :
    letI : LRV.Structure M := N
    letI : M ⊨ Axioms.ACVF := hN
    (@pullbackObject M sM hM S n (@rvObjectArity M sM S n U) E) ≅
      U.restrict (complement U (@liftLabelLocus M sM hM S n (@rvObjectArity M sM S n U) C))
        (complement_subset U _) := by
  have hEA : carrier E ⊆ carrier A := fun p hp => (Set.ext_iff.mp hpart p).mpr (Or.inr hp)
  let L := liftLabelLocus C
  let LE := liftLabelLocus E
  have hc := liftLabelLocus_subset h hEA
  have hp := normalizedPresentsLift_sublocus h hEA hE
  let e := pullbackPresentationIso hp
  have he := liftLabelLoci_complement h hpart hCE hC
  letI := N
  letI := hN
  let R := U.restrict LE hc
  let T := U.restrict (complement U L) (complement_subset U L)
  exact e.trans (rvIsoOfCarrierEq R.domain T.domain R.volume T.volume he (fun _ => rfl))

end IntegrationInACVF.Section6
