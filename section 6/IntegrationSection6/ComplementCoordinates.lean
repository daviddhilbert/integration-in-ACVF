import IntegrationSection6.PresentationCoordinates
import IntegrationSection6.LiftComplement

/-! The unchanged complementary chart projects out the canonical RV keys. -/
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

theorem liftComplementIso_labels {U : @RVObject M N S n}
    {A C E : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (hpart : carrier A = carrier C ∪ carrier E) (hCE : Disjoint (carrier C) (carrier E))
    (hC : IsRVPullback (carrier C)) (hE : IsRVPullback (carrier E))
    (a : rvObjectDomain (pullbackObject E)) :
    (@RVHom.map M N S n (pullbackObject E) _ (liftComplementIso h hpart hCE hC hE).hom a).val =
      fun j => a.val (Fin.natAdd n j) := by
  have hEA : carrier E ⊆ carrier A := fun p hp => (Set.ext_iff.mp hpart p).mpr (Or.inr hp)
  exact pullbackPresentationIso_labels (normalizedPresentsLift_sublocus h hEA hE) a

end IntegrationInACVF.Section6
