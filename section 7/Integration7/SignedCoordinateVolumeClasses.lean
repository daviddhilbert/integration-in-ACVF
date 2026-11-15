import Integration7.VolumeClassCoordinatePermutations
import Integration7.VolumeCoordinatePermutation
import Integration7.PermutationSignParameters
import Integration7.DefinableVolumeClassRescaling

/-! The exact determinant-density correction for RV coordinate order.
Signed coordinate reindexing gives an actual volume isomorphism before
normalization, in every positive degree and on the full quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)

private theorem permutationSignInverseDefinable (σ : Equiv.Perm (Fin (k+1))) :
    (C.base : Set M).Definable₁ LRV {((rvPermutationSign (M := M) σ)⁻¹).val} :=
  Set.Definable.singleton_of_mem LRV (rv_inv_mem_base C.base (rvPermutationSign_mem C.base σ))

def signedCoordinateVolumeObject
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    PositiveRVVolumeObject (M := M) (C.base : Set M) k :=
  (U.permuteVolume σ).rescaleDefinable (rvPermutationSign σ)⁻¹
    (permutationSignInverseDefinable C σ) (inv_ne_zero (rvPermutationSign_ne_zero σ))

def signedCoordinateVolumeIso
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    RVVolumeIso U (signedCoordinateVolumeObject C U σ) := by
  let f : U.underlying ≅ (U.permuteVolume σ).underlying :=
    rvFiniteIsoOfAmbient (rvReindexVolumeIso U.underlying.obj σ)
  exact RVVolumeIso.of_permuted_coordinates_full hc C f σ (fun _ => rfl) (fun _ => rfl)

def signedVolumeClassPermutationCorrection (σ : Equiv.Perm (Fin (k+1))) :
    PositiveVolumeBlowupClasses hc C k →+ PositiveVolumeBlowupClasses hc C k :=
    positiveVolumeClassRescaleDefinable hc C (rvPermutationSign σ)⁻¹
      (permutationSignInverseDefinable C σ) (inv_ne_zero (rvPermutationSign_ne_zero σ))

theorem signed_coordinate_volume_class_restore (σ : Equiv.Perm (Fin (k+1)))
    (x : PositiveVolumeBlowupClasses hc C k) :
    signedVolumeClassPermutationCorrection hc C σ (positiveVolumeClassPermute hc C σ x)=x := by
  induction x using Quotient.inductionOn with
  | h U => exact (positiveVolumeBlowupClass_iso hc C (signedCoordinateVolumeIso hc C U σ)).symm
end IntegrationInACVF.Section7
