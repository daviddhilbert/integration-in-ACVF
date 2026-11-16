module

public import Integration7.ContractionRetainedDensityLabels

@[expose] public section

/-! A fixed old RV label has that exact value on every label of the
actual raw and normalized contraction objects. Source representatives
are supplied by the actual surjective contraction maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a : ℕ} {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem raw_contraction_retained_label_value (C : StandardContraction A σ) (δ : Fin a)
    (η : RV (M := M)) (hη : ∀ p : A, p.val.2 δ = η) :
    ∀ u : rvObjectDomain C.contractionObject, u.val (suffixIndex C.program.rvArity_le δ) = η := by
  intro u
  obtain ⟨p,rfl⟩ := standard_raw_contraction_map_surjective C u
  change (C.toMap p).val.2 (suffixIndex C.program.rvArity_le δ) = η
  exact (C.program.oldLabels (vfPermutationBijection A σ p) δ).trans (hη p)

theorem normalized_contraction_retained_label_value (C : StandardContraction A σ) (δ : Fin a)
    (η : RV (M := M)) (hη : ∀ p : A, p.val.2 δ = η) :
    ∀ u : rvObjectDomain C.normalizedObject, u.val (FiniteRV.contractionOldLabelIndex C δ) = η := by
  intro u
  obtain ⟨p,rfl⟩ := standard_normalized_contraction_map_surjective C u
  rw [FiniteRV.contraction_oldLabels]
  exact hη p

end IntegrationInACVF.Section7
