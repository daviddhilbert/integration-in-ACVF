import IntegrationSection6.GammaSelectedLabelFibrePresentations
import IntegrationSection6.GammaPresentationBaseEquality
import IntegrationSection5.VFPermutation

/-! Reindexing VF parameters by a permutation preserves the precise
pointwise selected-volume hypothesis, including its named parameter base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}
open FiniteRV

theorem vfPermutationImage_row (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (x : Fin n → VF (M := M)) (r : Fin a → RV (M := M)) :
    (x,r) ∈ carrier (vfPermutationImage U σ) ↔ (x ∘ σ.symm,r) ∈ carrier U := by
  constructor
  · rintro ⟨u,hu⟩
    have he := (congrArg (vfPermutation σ.symm) hu).symm.trans (vfPermutation_inverse σ u.val)
    change vfPermutation σ.symm (x,r) ∈ carrier U
    exact he.symm ▸ u.property
  · intro h
    let u : U := ⟨(x ∘ σ.symm,r),h⟩
    refine ⟨u,?_⟩
    exact vfPermutation_inverse σ.symm (x,r)

theorem vfPermutationParameterBase (σ : Equiv.Perm (Fin n)) (x : Fin n → VF (M := M)) :
    (⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ : Base (M := M)) =
      ⟨B.real ∪ Set.range (fun j => (x (σ.symm j)).val),B.gamma⟩ := by
  apply congrArg (fun R => (⟨R,B.gamma⟩ : Base (M := M)))
  apply congrArg (B.real ∪ ·)
  ext c
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨σ j,by simp⟩
  · rintro ⟨j,rfl⟩
    exact ⟨σ.symm j,rfl⟩

def permutedFibrePresentation (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (ρ : Fin k → Fin a) (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B (vfPermutationImage U σ) ρ x) :
    SelectedLabelFibrePresentation B U ρ (x ∘ σ.symm) :=
  (P.congrFormula (Set.ext (vfPermutationImage_row U σ x))
    (fun r y => and_congr (vfPermutationImage_row U σ x r) Iff.rfl)).rebase (vfPermutationParameterBase σ x)

theorem vfPermutation_selected_finite (U : DefSet (M := M) S n a) (σ : Equiv.Perm (Fin n))
    (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier (vfPermutationImage U σ) ∧ r ∘ ρ = t}.Finite := by
  intro x t
  have he : {r : Fin a → RV (M := M) | (x,r) ∈ carrier (vfPermutationImage U σ) ∧ r ∘ ρ = t} =
      {r | (x ∘ σ.symm,r) ∈ carrier U ∧ r ∘ ρ = t} :=
    Set.ext (fun r => and_congr (vfPermutationImage_row U σ x r) Iff.rfl)
  rw [he]
  exact hfin _ t

theorem gamma_permuted_pointwise_comparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)
    (U : DefSet (M := M) S n a) (V : DefSet (M := M) S n b) (σ : Equiv.Perm (Fin n))
    (ρ : Fin k → Fin a) (τ : Fin k → Fin b)
    (hCommon : ∀ x : Fin n → VF (M := M),
      ∀ P : SelectedLabelFibrePresentation B U ρ x, ∀ Q : SelectedLabelFibrePresentation B V τ x,
      GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma)
    (x : Fin n → VF (M := M))
    (P : SelectedLabelFibrePresentation B (vfPermutationImage U σ) ρ x)
    (Q : SelectedLabelFibrePresentation B (vfPermutationImage V σ) τ x) :
    GammaIsp hκ hs h00 (small_union_range hκ B.real hreal (fun j => (x j).val)) P.toGamma Q.toGamma := by
  have h := hCommon (x ∘ σ.symm) (permutedFibrePresentation U σ ρ x P) (permutedFibrePresentation V σ τ x Q)
  unfold permutedFibrePresentation at h
  have h' := (gammaIsp_rebase_iff hκ hs h00
    (small_union_range hκ B.real hreal (fun j => (x j).val))
    (small_union_range hκ B.real hreal (fun j => (x (σ.symm j)).val))
    (vfPermutationParameterBase (B := B) σ x) _ _).mpr h
  simpa only [GammaFiniteGraphPresentation.congrFormula_toGamma] using h'

end IntegrationInACVF.Section6
