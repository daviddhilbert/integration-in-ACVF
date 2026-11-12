import IntegrationSection6.LiftRVImage

/-! Recovering old labels from the full key uses the literal tail projection. -/
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

theorem pullbackPresentationIso_labels {U : @RVObject M N S n}
    {A : SpecialTransformations.Section5.DefSet (M := M) S n (rvObjectArity U)}
    (h : @PresentsLift M N hN S n U (normalizedPointSet A))
    (a : rvObjectDomain (pullbackObject A)) :
    (@RVHom.map M N S n (pullbackObject A) U (pullbackPresentationIso h).hom a).val =
      fun j => a.val (Fin.natAdd n j) := by
  have he := normalizedPresentsLift_key_domains h
  have ha := (Set.ext_iff.mp he a.val).mp a.property
  exact @canonicalRVKeyIso_inv_labels M N hN S n U ⟨a.val,ha⟩

end IntegrationInACVF.Section6
