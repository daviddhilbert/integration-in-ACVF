import Integration7.BoundedVolumeIsoCertificates
import Integration7.EssentialGammaWeight
import Integration7.GammaVolumeCriterion

/-! Exact finite-certificate characterization of a volume isomorphism
with its underlying essential chart fixed. Gamma weight is pointwise;
the RV equation follows from the actual polynomial chart certificate. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9
open scoped BigOperators

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem gammaVolumeEquation_of_weight
    {U V : PositiveRVVolumeObject (M := M) S k} (e : U.essential ≅ V.essential)
    (u : U.essential.obj.domain)
    (h : essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u)) :
    Values.vrv (U.essentialForm.value u) =
      Values.vrv (V.essentialForm.value (finiteIsoMap e u)) *
        (rvGammaJacobian (U.essential.obj.value u)
          (V.essential.obj.value (finiteIsoMap e u))
          (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e u))).val := by
  apply gammaVolumeEquation_of_absoluteRatio e u
  have hV : RVOperations.absoluteHom (V.essentialForm.value (finiteIsoMap e u)) ≠ 0 :=
    (RVOperations.absolute_eq_zero _).not.mpr (V.essentialForm_nonzero _)
  have hU : (∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (RVOperations.absolute_eq_zero _).not.mpr
      ((rv_nonzero_iff_raw _).mpr (U.essential_nonzero u i)))
  rw [volumeRatio,map_div₀]
  apply (div_eq_div_iff hV hU).mpr
  exact h.trans (mul_comm _ _)

def RVVolumeIsoCertificate.toIso {U V : PositiveRVVolumeObject (M := M) S k}
    {e : U.essential ≅ V.essential} (H : RVVolumeIsoCertificate U V e)
    (hΓ : ∀ u, essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u)) : RVVolumeIso U V where
  iso := e
  gamma u := gammaVolumeEquation_of_weight e u (hΓ u)
  rv := H.rv

@[simp] theorem RVVolumeIsoCertificate.toIso_underlying
    {U V : PositiveRVVolumeObject (M := M) S k} {e : U.essential ≅ V.essential}
    (H : RVVolumeIsoCertificate U V e)
    (hΓ : ∀ u, essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u)) :
    (H.toIso hΓ).iso = e := rfl

theorem rvVolumeIso_finite_certificate_iff
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (e : U.essential ≅ V.essential) :
    (∃ f : RVVolumeIso U V, f.iso = e) ↔
      (∀ u, essentialGammaWeight U u = essentialGammaWeight V (finiteIsoMap e u)) ∧
        Nonempty (RVVolumeIsoCertificate U V e) := by
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨f.essentialGammaWeight,f.exists_finite_certificate hc C⟩
  · rintro ⟨hΓ,⟨H⟩⟩
    exact ⟨H.toIso hΓ,rfl⟩

end IntegrationInACVF.Section7
