import Integration7.GenericPermutationRVJacobian
import Integration7.RVVolumeInverse
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.Section7
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open scoped BigOperators
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem volumeRatio_of_permuted_density (U V : PositiveRVVolumeObject (M := M) S k)
    (f : U.essential ≅ V.essential) (e : Equiv.Perm (Fin (k+1)))
    (hφ : ∀ u, V.essentialForm.value (finiteIsoMap f u) =
      (rvPermutationSign e)⁻¹ * U.essentialForm.value u) (u : U.essential.obj.domain) :
    volumeRatio U V f u = rvPermutationSign e := by
  apply (div_eq_iff (V.essentialForm_nonzero _)).mpr
  rw [hφ, ← mul_assoc, mul_inv_cancel₀ (rvPermutationSign_ne_zero e), one_mul]

def RVVolumeIso.of_permuted_coordinates
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : U.essential ≅ V.essential) (e : Equiv.Perm (Fin (k+1)))
    (hcoord : ∀ u, V.essential.obj.value (finiteIsoMap f u) = U.essential.obj.value u ∘ e)
    (hφ : ∀ u, V.essentialForm.value (finiteIsoMap f u) =
      (rvPermutationSign e)⁻¹ * U.essentialForm.value u) : RVVolumeIso U V where
  iso := f
  gamma u := by
    apply gammaVolumeEquation_of_absoluteRatio f u
    rw [volumeRatio_of_permuted_density U V f e hφ, rvPermutationSign_absolute, hcoord]
    have hprod : (∏ i, RVOperations.absoluteHom ((U.essential.obj.value u ∘ e) i)) =
        ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i) :=
      Equiv.prod_comp e (fun i => RVOperations.absoluteHom (U.essential.obj.value u i))
    have hnonzero : (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      apply (RVOperations.absolute_eq_zero _).not.mpr
      intro h
      exact U.essential_nonzero u i ((congrArg Subtype.val h).trans RVOperations.zero_val)
    exact (div_self hnonzero).symm.trans (congrArg
      (fun z => z / ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) hprod.symm)
  rv := (rvJacobian_coordinatePermutation_ae hc C (Nat.zero_lt_succ k) f e
    U.essential_nonzero V.essential_nonzero hcoord).mono (fun u hu => by
      rw [volumeRatio_of_permuted_density U V f e hφ]
      exact hu)

def RVVolumeIso.of_permuted_coordinates_full
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : U.underlying ≅ V.underlying) (e : Equiv.Perm (Fin (k+1)))
    (hcoord : ∀ u, V.underlying.obj.value (finiteIsoMap f u) = U.underlying.obj.value u ∘ e)
    (hφ : ∀ u, V.form.value (finiteIsoMap f u) = (rvPermutationSign e)⁻¹ * U.form.value u) : RVVolumeIso U V := by
  apply of_permuted_coordinates hc C (rvFiniteEssentialIso f) e
  · intro u
    exact hcoord ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩
  · intro u
    exact hφ ⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩
end IntegrationInACVF.Section7
