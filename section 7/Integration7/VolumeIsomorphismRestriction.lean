import Integration7.VolumeAlmostEverywhere
import Integration7.RVJacobianRestriction
import Integration7.GammaVolumeCriterion
import Section9.GenericRVJacobian

/-! Restriction along an actual definable injection. Generic existence on
the smaller correspondence and tangent inclusion identify its Jacobian. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def RVVolumeIso.of_injective_restriction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V L R : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (f : RVVolumeIso U V) (e : L.essential ≅ R.essential)
    (i : Map L.essential.obj.domain U.essential.obj.domain) (hi : Function.Injective i)
    (hsource : ∀ u, U.essential.obj.value (i u) = L.essential.obj.value u)
    (htarget : ∀ u, V.essential.obj.value (finiteIsoMap f.iso (i u)) =
      R.essential.obj.value (finiteIsoMap e u))
    (hφsource : ∀ u, U.essentialForm.value (i u) = L.essentialForm.value u)
    (hφtarget : ∀ u, V.essentialForm.value (finiteIsoMap f.iso (i u)) =
      R.essentialForm.value (finiteIsoMap e u)) : RVVolumeIso L R where
  iso := e
  gamma u := by
    apply gammaVolumeEquation_of_absoluteRatio e u
    have h := f.absolute_volumeRatio (i u)
    simpa only [volumeRatio, hφsource, hφtarget, hsource, htarget] using h
  rv := by
    obtain ⟨ω, D, hD, hd, hω⟩ := exists_definable_generic_RVJacobian hc C (Nat.zero_lt_succ k)
      e L.essential_nonzero R.essential_nonzero
    have hdefined : RVAlmostEverywhere L.essential.obj.domain (k + 1) (fun u =>
        IsRVJacobianAt (volumeCorrespondence (finiteIsoMap e)).carrier
          (L.essential.obj.value u) (R.essential.obj.value (finiteIsoMap e u)) ((ω u).val 0)) :=
      ⟨D, hD, hd, hω⟩
    have hfull := RVAlmostEverywhere.pullback_injective i hi f.rv
    have hsub : (volumeCorrespondence (finiteIsoMap e)).carrier ⊆
        (volumeCorrespondence (finiteIsoMap f.iso)).carrier := by
      rintro z ⟨u, rfl⟩
      refine ⟨i u, ?_⟩
      change productTuple (U.essential.obj.value (i u))
        (V.essential.obj.value (finiteIsoMap f.iso (i u))) = _
      rw [hsource, htarget]
    apply RVAlmostEverywhere.mono (hfull.and hc C hdefined)
    rintro u ⟨hfull, hlocal⟩
    rw [hsource, htarget] at hfull
    have he := rvJacobian_eq_of_subset hsub hlocal hfull
    have hratio : volumeRatio U V f.iso (i u) = volumeRatio L R e u := by
      unfold volumeRatio
      rw [hφsource, hφtarget]
    have hvalue := he.trans hratio
    rw [← hvalue]
    exact hlocal

end IntegrationInACVF.Section7
