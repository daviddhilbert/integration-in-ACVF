module

public import Integration7.PullbackCoordinateVolumeObjects
public import IntegrationSection6.FiniteGammaObjects
public import IntegrationSection5.QuotientBijection
public import IntegrationSection5.RVContractionGamma
public import Integration7.GammaCoordinateDensityGraphs
public import Integration7.GammaVolumeSliceAssemblyGeometry

@[expose] public section

/-! The actual coordinate-density volume object of a Gamma pullback
with finite volume fibres has complete original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {k a : ℕ}

def pullbackCoordinateGammaObject
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (k+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hAF : @SpecialTransformations.DefinableGeometry.Map.FiniteFibres LRV M
      (@CanonicalStructure.normalize M sM) _ _ (C.base : Set M) _ _ (rvObjectVolume (pullbackObject A)))
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    GammaVolumeObjects G (C.base : Set M) k := by
  let U := (FiniteRV.gammaPullbackAt hGC A hA hAF).toGamma
  have hNZ : ∀ u : rvObjectDomain U.object, (u.val (Fin.natAdd (k+1) δ)).val ≠ iRVZero := by
    intro u
    obtain ⟨p,rfl⟩ := rawKeyImage_surjective A u
    erw [rawKeyMap_apply]
    simpa only [Fin.append_right] using hδ p
  exact ⟨pullbackCoordinateVolumeObject hc A hAF δ hδ,
    gamma_coordinate_density_object_graphs (e := k) (k := 0) hc C U (Set.Subset.refl _)
      (Fin.natAdd (k+1) δ) hNZ⟩

end IntegrationInACVF.Section7
