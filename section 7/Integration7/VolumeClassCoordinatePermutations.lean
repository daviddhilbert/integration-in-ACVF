import Integration7.GammaPermutedVolumeObjects
import Integration7.VolumeBlowupCoordinatePermutations
import Integration7.VolumeBlowupClasses

/-! Unchanged-density coordinate reindexing acts on the common-blowup
quotient. This is an equivalence of the quotient, and is not an assertion
that an individual unsigned permutation is a volume isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem VolumeBlowupEquivalent.permuteVolume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (e : Equiv.Perm (Fin (k+1))) :
    VolumeBlowupEquivalent (U.permuteVolume e) (V.permuteVolume e) :=
  h.of_permuted_coordinate_charts hc C e
    (rvFiniteIsoOfAmbient (rvReindexVolumeIso U.underlying.obj e))
    (rvFiniteIsoOfAmbient (rvReindexVolumeIso V.underlying.obj e))
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

def positiveVolumeClassPermute
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (e : Equiv.Perm (Fin (k+1))) :
    PositiveVolumeBlowupClasses hc C k → PositiveVolumeBlowupClasses hc C k :=
  Quotient.map (fun U => U.permuteVolume e) (fun _ _ h => h.permuteVolume hc C e)

theorem positive_volume_class_permute_representative
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (e : Equiv.Perm (Fin (k+1)))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    positiveVolumeClassPermute hc C e (positiveVolumeBlowupClass hc C U) =
      positiveVolumeBlowupClass hc C (U.permuteVolume e) := rfl

def volumePermutationCancelIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (e : Equiv.Perm (Fin (k+1))) :
    RVVolumeIso ((U.permuteVolume e).permuteVolume e.symm) U := by
  let W := (U.permuteVolume e).permuteVolume e.symm
  let f : Map W.underlying.obj.domain U.underlying.obj.domain := Map.id _
  have hCoord : ∀ u, U.underlying.obj.value (f u) = W.underlying.obj.value u := by
    intro u
    funext i
    change U.underlying.obj.value u i = U.underlying.obj.value u (e (e.symm i))
    rw [e.apply_symm_apply]
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)

def positiveVolumeClassPermutationEquiv
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (e : Equiv.Perm (Fin (k+1))) :
    PositiveVolumeBlowupClasses hc C k ≃ PositiveVolumeBlowupClasses hc C k where
  toFun := positiveVolumeClassPermute hc C e
  invFun := positiveVolumeClassPermute hc C e.symm
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h U => exact positiveVolumeBlowupClass_iso hc C (volumePermutationCancelIso hc C U e)
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h U => exact positiveVolumeBlowupClass_iso hc C (volumePermutationCancelIso hc C U e.symm)

end IntegrationInACVF.Section7
