import Integration7.RelativeMixedFibreJacobians
import Integration7.MixedRetainedLabelVolumeForms
import Integration7.NativeVolumeDomains
import Integration7.VFAlmostEverywhere
import Integration7.VFVolumeBijections

/-! Restricting the actual measure equation to a coordinate fibre whose
intersection with the witnessed exception is VF-small. This keeps the
exception explicit instead of asserting preservation on every fibre. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b : ℕ}

theorem coordinate_fibre_retained_density_nonzero
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a)
    (hω : ∀ q, ω.value q = q.val.2 δ) (i : Fin n) (u : Fin n → VF (M := M)) :
    ∀ p : rawSpecialSet hc (coordinateFibre A i u), (p.val.2 δ).val ≠ iRVZero := by
  intro p
  let q : rawSpecialSet hc A := ⟨coordinateInsert i u p.val,p.property⟩
  exact (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero q ((hω q).trans h))

def coordinateFibreRetainedVolumeForm
    (hc : CanonicalStructure.IsCanonical (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) S n a)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a)
    (hω : ∀ q, ω.value q = q.val.2 δ) (i : Fin n) (u : Fin n → VF (M := M)) :
    VolumeForm (rawSpecialSet hc (coordinateFibre A i u)) :=
  mixedRetainedLabelVolumeForm _ δ (coordinate_fibre_retained_density_nonzero hc A ω δ hω i u)

set_option maxHeartbeats 1600000 in
theorem relative_volume_on_fibre_of_small_exception
    (hc : CanonicalStructure.IsCanonical (M := M))
    {A : SpecialTransformations.Section5.DefSet (M := M) S n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) S n b}
    (f : SpecialTransformations.Section5.Map A B) (i : Fin n) (hi : UnaryRelative f i)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (D : DefSet (rawMixedSpace (M := M) n a) S)
    (hglobal : ∀ q : rawSpecialSet hc A, q.val ∉ D.carrier →
      ∃ J : SpecialTransformations.Milestone0.Transfer.VFType (M := M),
        HasMixedVFJacobianAt (rawSpecialMap hc f) q J ∧
        ω.value q = π.value ((rawSpecialMap hc f) q) * CanonicalRV.encodedRv J)
    (u : Fin n → VF (M := M))
    (hsmall : vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1)
      (rawSpecialSet hc (coordinateFibre (nativeMixedVolumeDomain hc D) i u)) < 1) :
    PreservesVFVolume (coordinateFibreRetainedVolumeForm hc A ω δ hω i u)
      (coordinateFibreRetainedVolumeForm hc B π ε hπ i u)
      (rawSpecialMap hc (coordinateFibreMap f i hi u)) := by
  apply VFAlmostEverywhere.of_exception
    (rawSpecialSet hc (coordinateFibre (nativeMixedVolumeDomain hc D) i u)) hsmall
  intro p hp
  let q : rawSpecialSet hc A := ⟨coordinateInsert i u p.val,p.property⟩
  have hq : q.val ∉ D.carrier := fun h => hp h
  obtain ⟨J,hJ,hMeasure⟩ := hglobal q hq
  refine ⟨J,relative_mixed_vf_jacobian_on_coordinate_fibre hc f i hi u p J hJ,?_⟩
  rw [hω,hπ] at hMeasure
  exact hMeasure

end IntegrationInACVF.Section7
