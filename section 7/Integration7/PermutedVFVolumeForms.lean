import Integration7.PermutedMixedVolumeJacobians
import Integration7.VFVolumeBijections

/-! Simultaneous VF-coordinate permutation preserves the original volume
equation. The same Jacobian determinant is retained, with the forms
pulled back along the actual inverse coordinate bijections. -/
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

def permutedVFVolumeForm (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S n a) (ω : VolumeForm (rawSpecialSet hc U))
    (σ : Equiv.Perm (Fin n)) : VolumeForm (rawSpecialSet hc (vfPermutationImage U σ)) :=
  ω.pullback (rawSpecialMap hc (Map.inverse (vfPermutationBijection U σ) (vfPermutationBijection_bijective U σ)))

theorem permuted_vf_volume_form_retained
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : DefSet (M := M) S n a) (ω : VolumeForm (rawSpecialSet hc U))
    (σ : Equiv.Perm (Fin n)) (δ : Fin a)
    (hω : ∀ q, ω.value q = q.val.2 δ)
    (p : rawSpecialSet hc (vfPermutationImage U σ)) :
    (permutedVFVolumeForm hc U ω σ).value p = p.val.2 δ := by
  let P := vfPermutationBijection U σ
  let hP := vfPermutationBijection_bijective U σ
  change ω.value (Map.inverse P hP p) = p.val.2 δ
  exact (hω _).trans (congrArg (fun z => z.val.2 δ) (Map.apply_inverse P hP p))

set_option maxHeartbeats 2400000 in
theorem preserves_vf_volume_conjugate_permutation
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U : DefSet (M := M) S n a} {V : DefSet (M := M) S n b}
    (f : Map U V) (σ : Equiv.Perm (Fin n))
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f)) :
    PreservesVFVolume (permutedVFVolumeForm hc U ω σ) (permutedVFVolumeForm hc V π σ)
      (rawSpecialMap hc (vfPermutedMap f σ)) := by
  let P := vfPermutationBijection U σ
  let hP := vfPermutationBijection_bijective U σ
  let Pinv := Map.inverse P hP
  have hi : Function.Injective Pinv := by
    intro x y h
    exact (Map.apply_inverse P hP x).symm.trans ((congrArg P h).trans (Map.apply_inverse P hP y))
  have hPull := VFAlmostEverywhere.pullback_injective (rawSpecialMap hc Pinv) hi hm
  apply hPull.mono
  rintro p ⟨J,hJ,hVolume⟩
  refine ⟨J,mixed_vf_jacobian_conjugate_permutation hc f σ p J hJ,?_⟩
  let Q := vfPermutationBijection V σ
  let hQ := vfPermutationBijection_bijective V σ
  have hTarget : Map.inverse Q hQ (vfPermutedMap f σ p) = f (Pinv p) :=
    Map.inverse_apply Q hQ (f (Pinv p))
  change ω.value (Pinv p) = π.value (Map.inverse Q hQ (vfPermutedMap f σ p)) * CanonicalRV.encodedRv J
  rw [hTarget]
  exact hVolume

end IntegrationInACVF.Section7
