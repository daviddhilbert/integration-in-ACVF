import IntegrationSection6.PartialFamilyLiftIsomorphisms
import IntegrationSection6.GammaCoordinateValues

/-! The relative representative isomorphism preserves every frozen VF
parameter, so its restriction is an actual isomorphism on each fibre. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p n a l : ℕ}
variable {U : DefSet (M := M) S (p+n) a} {V : DefSet (M := M) S p l}

theorem activeFrozenShuffle_symm_prefix (p n : ℕ) (j : Fin p) :
    (activeFrozenShuffle p n).symm (Fin.castAdd n j) = frozenIndex p n j := by
  have h := congrArg (activeFrozenShuffle p n).symm (activeFrozenShuffle_frozen p n j)
  rw [Equiv.symm_apply_apply] at h
  exact h.symm

theorem gammaPartialFamilyLiftIso_frozen (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (A : Set (Point (M := M) p 0)) (T : PartialContractionProgram S p (n := n) U V)
    (hT : GammaPartialProgramDefinable B T)
    (hUA : ∀ u : U, (fun j => vfAt u.val (frozenIndex p n j),Fin.elim0) ∈ A)
    (u : U) (j : Fin p) :
    vfAt ((gammaPartialFamilyLiftIso hBS hU A T hT hUA).equiv u).val (Fin.castAdd n j) =
      vfAt u.val (frozenIndex p n j) := by
  unfold gammaPartialFamilyLiftIso
  rw [gammaIsoCongrTarget_value]
  change vfAt ((gammaVFCoordinateIso (carrier T.naturalImage)
      ((gammaPartialNaturalIso hBS T hT).target_definable (gammaLogicInput B))
      (activeFrozenShuffle p n).symm).equiv ((gammaPartialNaturalIso hBS T hT).equiv u)).val
      (Fin.castAdd n j) = _
  rw [gammaVFCoordinateIso_value]
  change vfAt (T.naturalMap u).val ((activeFrozenShuffle p n).symm (Fin.castAdd n j)) = _
  rw [activeFrozenShuffle_symm_prefix]
  exact T.naturalMap_frozen u j

end IntegrationInACVF.Section6
