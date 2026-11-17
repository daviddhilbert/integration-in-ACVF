module

public import Integration7.PositiveVFVolumePermutations
public import Integration7.NativeRVGraphVolumeRefinements
public import IntegrationSection6.PermutationFiniteFibres

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Raw and native VF-permuted domains are identical on points. Their
transported volume forms therefore give an actual identity-coordinate
VF volume bijection, retaining any specified RV coordinate density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a k : ℕ}

theorem raw_native_vf_permutation_carrier
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n a) S) (σ : Equiv.Perm (Fin n)) :
    (rawSpecialSet hc (vfPermutationImage (nativeMixedVolumeDomain hc A) σ)).carrier =
      (mixedVFPermutationDomain A σ).carrier := by
  ext q
  change (q.1,q.2) ∈ carrier (vfPermutationImage (nativeMixedVolumeDomain hc A) σ) ↔
    (q.1,q.2) ∈ (mixedVFPermutationDomain A σ).carrier
  rw [vfPermutationImage_row,mem_mixed_vf_permutation_domain]
  rfl

def nativePermutedVFVolumeObject
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveVFVolumeObject (M := M) S k) (σ : Equiv.Perm (Fin (k+1))) :
    PositiveVFVolumeObject (M := M) S k :=
  nativeMixedVFVolumeObject hc (vfPermutationImage (nativeMixedVolumeDomain hc U.domain) σ)
    (vfPermutation_finite_rv_fibres (nativeMixedVolumeDomain hc U.domain) σ U.finite_labels)
    ((U.permuteVF σ).form.pullback (Map.inclusion (raw_native_vf_permutation_carrier hc U.domain σ).le))

def nativePermutedVFVolumeBijection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (σ : Equiv.Perm (Fin (k+1))) :
    VFVolumeBijection (U.permuteVF σ) (nativePermutedVFVolumeObject hc U σ) := by
  let h := raw_native_vf_permutation_carrier hc U.domain σ
  let f : Map (U.permuteVF σ).domain (nativePermutedVFVolumeObject hc U σ).domain := Map.inclusion h.ge
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have hv := congrArg Subtype.val he
      exact Subtype.ext hv
    · intro q
      exact ⟨⟨q.val,h.le q.property⟩,rfl⟩
  exact VFVolumeBijection.of_preserving_vf_and_density hc C f hf (fun _ => rfl) (fun _ => rfl)

theorem native_permuted_vf_coordinate_density
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveVFVolumeObject (M := M) S k) (σ : Equiv.Perm (Fin (k+1)))
    (δ : Fin U.arity) (hδ : ∀ q, U.form.value q=q.val.2 δ)
    (q : (nativePermutedVFVolumeObject hc U σ).domain) :
    (nativePermutedVFVolumeObject hc U σ).form.value q=q.val.2 δ := by
  let r : (U.permuteVF σ).domain := ⟨q.val,(raw_native_vf_permutation_carrier hc U.domain σ).le q.property⟩
  exact (U.permuteVF_density σ r).trans (hδ _)

end IntegrationInACVF.Section7
