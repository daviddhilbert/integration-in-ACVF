import Integration7.UnaryContractionVolumeMaps
import IntegrationSection6.FiniteSelectedContractions

/-! Every normalized RV contraction label has a source representative.
Consequently a retained nonzero density stays nonzero on the entire RV
domain, including labels whose VF volume coordinate is zero. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem standard_raw_contraction_map_surjective (T : StandardContraction A σ) :
    Function.Surjective T.rawContractionMap := by
  intro u
  obtain ⟨q,hq⟩ := u.property
  obtain ⟨p,hp⟩ := (T.program.surjective.comp (vfPermutationBijection_bijective A σ).2) q
  refine ⟨p,Subtype.ext ?_⟩
  change (rawLabelMap T.target (T.toMap p)).val = u.val
  change T.toMap p = q at hp
  rw [hp]
  exact hq

theorem standard_normalized_contraction_map_surjective (T : StandardContraction A σ) :
    Function.Surjective T.normalizedContractionMap :=
  (@Section6.iso_map_bijective M N hN S n T.contractionObject T.normalizedObject T.normalizationIso).2.comp
    (standard_raw_contraction_map_surjective T)

theorem normalized_contraction_retained_density_nonzero
    (T : StandardContraction A σ) (δ : Fin a)
    (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    ∀ u : rvObjectDomain T.normalizedObject,
      (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero := by
  intro u
  obtain ⟨p,rfl⟩ := standard_normalized_contraction_map_surjective T u
  rw [FiniteRV.contraction_oldLabels]
  exact hδ p

end IntegrationInACVF.Section7
