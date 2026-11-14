import Integration7.GammaVolumeCriterion
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r n k : ℕ}

theorem RVAlmostEverywhere.of_dim_lt (A : DefSet (rawRVSpace (M := M) r) S)
    (n : ℕ) (hd : rvDim A < n) (P : A → Prop) : RVAlmostEverywhere A n P :=
  ⟨A,Set.Subset.refl _,hd,fun p hp => False.elim (hp p.property)⟩

def RVVolumeIso.of_gamma_of_lower_rvDim {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (hd : rvDim U.essential.obj.domain < k+1)
    (hΓ : ∀ u : U.essential.obj.domain,
      Values.vrv (U.essentialForm.value u) = Values.vrv (V.essentialForm.value (finiteIsoMap e u)) *
        (rvGammaJacobian (U.essential.obj.value u) (V.essential.obj.value (finiteIsoMap e u))
          (U.essential_nonzero u) (V.essential_nonzero (finiteIsoMap e u))).val) : RVVolumeIso U V where
  iso := e
  gamma := hΓ
  rv := RVAlmostEverywhere.of_dim_lt U.essential.obj.domain (k+1) hd _

def RVVolumeIso.of_absoluteRatio_of_lower_rvDim {U V : PositiveRVVolumeObject (M := M) S k}
    (e : U.essential ≅ V.essential) (hd : rvDim U.essential.obj.domain < k+1)
    (h : ∀ u : U.essential.obj.domain,
      RVOperations.absoluteHom (volumeRatio U V e u) =
        (∏ i, RVOperations.absoluteHom (V.essential.obj.value (finiteIsoMap e u) i)) /
          ∏ i, RVOperations.absoluteHom (U.essential.obj.value u i)) : RVVolumeIso U V :=
  RVVolumeIso.of_gamma_of_lower_rvDim e hd (fun u => gammaVolumeEquation_of_absoluteRatio e u (h u))
end IntegrationInACVF.Section7
