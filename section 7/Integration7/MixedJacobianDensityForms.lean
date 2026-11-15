import Integration7.NonzeroScalarRVMaps
import Integration7.MixedDifferentiabilityAlmostEverywhere
import Section9.MixedJacobianValue

/-! A genuine definable density representing the VF Jacobian of a
bijection almost everywhere. Its exceptional zero values are replaced by1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a b : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n a) S}
variable {B : DefSet (rawMixedSpace (M := M) n b) S}

def mixedJacobianValueMap (f : Map A B) : Map A (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  Classical.choose (exists_totalMixedJacobianMap f)

theorem mixed_jacobian_value_map_of_derivative (f : Map A B) (p : A)
    (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) :
    (mixedJacobianValueMap f p).val 0 = (LinearMap.toMatrix' L).det :=
  Classical.choose_spec (exists_totalMixedJacobianMap f) p L hL

def mixedJacobianDensityForm (f : Map A B) : VolumeForm A where
  map := (nonzeroRVScalarMap S).comp ((scalarEncodedRVMap S).comp (mixedJacobianValueMap f))
  nonzero p := nonzero_rv_scalar_map_nonzero S _

theorem mixed_jacobian_density_form_of_derivative (f : Map A B) (p : A)
    (L : (Fin n → VFType (M := M)) →ₗ[VFType (M := M)] (Fin n → VFType (M := M)))
    (hL : HasMixedVFDerivativeAt f p L) (h0 : (LinearMap.toMatrix' L).det ≠ 0) :
    (mixedJacobianDensityForm f).value p = CanonicalRV.encodedRv (LinearMap.toMatrix' L).det := by
  have hj := mixed_jacobian_value_map_of_derivative f p L hL
  have hnz : ((scalarEncodedRVMap S) (mixedJacobianValueMap f p)).val 0 ≠ 0 := by
    rw [scalar_encoded_rv_map_value,hj]
    exact (RVOperations.rv_ne_zero _).mpr h0
  change (nonzeroRVScalarMap S ((scalarEncodedRVMap S) (mixedJacobianValueMap f p))).val 0 = _
  rw [nonzero_rv_scalar_map_of_nonzero S _ hnz,scalar_encoded_rv_map_value,hj]

theorem mixed_bijective_jacobian_density_ae
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hn : 0 < n)
    {A : DefSet (rawMixedSpace (M := M) n a) (C.base : Set M)}
    {B : DefSet (rawMixedSpace (M := M) n b) (C.base : Set M)}
    (f : Map A B) (hf : Function.Bijective f) :
    VFAlmostEverywhere A (fun p => ∃ J : VFType (M := M),
      HasMixedVFJacobianAt f p J ∧ J ≠ 0 ∧
        (mixedJacobianDensityForm f).value p = CanonicalRV.encodedRv J) := by
  have hD := mixed_differentiability_almost_everywhere hc C hn f
  have hN := mixed_bijective_jacobian_nonzero_ae hc C hn f hf
  apply (vfAlmostEverywhere_and hc C hD hN).mono
  rintro p ⟨⟨L,hL⟩,J,hJ,hJ0⟩
  have hLJ : HasMixedVFJacobianAt f p (LinearMap.toMatrix' L).det := by
    obtain ⟨F,hF,hD⟩ := hL
    exact ⟨F,hF,hD.hasJacobianAt⟩
  have he : (LinearMap.toMatrix' L).det = J := hLJ.unique hJ
  refine ⟨J,hJ,hJ0,?_⟩
  rw [mixed_jacobian_density_form_of_derivative f p L hL (he ▸ hJ0),he]

end IntegrationInACVF.Section7
