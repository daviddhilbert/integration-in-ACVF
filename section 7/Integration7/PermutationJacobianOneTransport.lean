module

public import Integration7.PermutedMixedVolumeJacobians
public import Integration7.VFAlmostEverywhere

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual full mixed Jacobian-one condition is invariant under
simultaneous permutation of the source and target VF coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

theorem vf_jacobian_one_conjugate_permutation
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (f : Map U V) (σ : Equiv.Perm (Fin n))
    (hJ : VFAlmostEverywhere (rawSpecialSet hc U)
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc f) p 1)) :
    VFAlmostEverywhere (rawSpecialSet hc (vfPermutationImage U σ))
      (fun p => HasMixedVFJacobianAt (rawSpecialMap hc (vfPermutedMap f σ)) p 1) := by
  let P := vfPermutationBijection U σ
  let hP := vfPermutationBijection_bijective U σ
  let g := Map.inverse P hP
  have hg : Function.Injective (rawSpecialMap hc g) := by
    intro p q he
    have h := congrArg P he
    exact (Map.apply_inverse P hP p).symm.trans (h.trans (Map.apply_inverse P hP q))
  exact (hJ.pullback_injective (rawSpecialMap hc g) hg).mono
    (fun p h => mixed_vf_jacobian_conjugate_permutation hc f σ p 1 h)

end IntegrationInACVF.Section7
