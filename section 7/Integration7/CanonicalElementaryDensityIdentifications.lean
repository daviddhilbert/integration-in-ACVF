import Integration7.CanonicalGammaElementaryLiftVolumes
import Integration7.VolumeRelabeling

/-! The literal density used by the focus lift is the density of the
actual canonical elementary volume object. The identifying RV map is
the identity on every full label tuple, including degenerate ones. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem canonical_elementary_density_identification
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k)) :
    Nonempty (RVVolumeIso (canonicalGammaElementaryDensityObject hc C U ω hAd)
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hAd))) := by
  let X := canonicalGammaElementaryDensityObject hc C U ω hAd
  let Y := elementaryVolumeObject C
    (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (canonicalGammaElementaryAdmissible hc C U ω hAd)
  have hDomain := canonical_gamma_elementary_domain hc C U ω hAd
  let f : Map X.underlying.obj.domain Y.underlying.obj.domain := Map.inclusion hDomain.le
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv := congrArg (fun w : Y.underlying.obj.domain => w.val) h
      exact Subtype.ext hv
    · intro v
      exact ⟨⟨v.val,hDomain.ge v.property⟩,rfl⟩
  have hcoord (u : X.underlying.obj.domain) : Y.underlying.obj.value (f u) = X.underlying.obj.value u :=
    (canonical_elementary_coordinates hc U.object.obj (Fin.last k) u).symm
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)
  refine ⟨RVVolumeIso.of_preserving_coordinates_full hc C e hcoord ?_⟩
  intro u
  change ω.value (Section6.elementaryProjection (canonicalRVObject hc U.object.obj) (Fin.last k) (f u)) =
    ω.value (canonicalRawRVMap hc (@Section6.elementaryProjection M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)) u)
  apply congrArg ω.value
  apply Subtype.ext
  exact (Section6.elementaryProjection_labels (canonicalRVObject hc U.object.obj) (Fin.last k) (f u)).trans
    (@Section6.elementaryProjection_labels M (@CanonicalStructure.normalize M sM)
      (@CanonicalStructure.normalized_model M sM hM) (C.base : Set M) (k+1) U.object.obj (Fin.last k)
      ⟨u.val,u.property⟩).symm

end IntegrationInACVF.Section7
