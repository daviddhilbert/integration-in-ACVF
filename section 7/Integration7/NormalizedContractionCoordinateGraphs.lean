import Integration7.ConstantCoordinateDensityObjects
import Integration7.GammaCoordinateDensityGraphs
import Integration7.GammaVolumeObjectGraphs
import IntegrationSection5.StandardContractionGammaNormalization

/-! Complete original-Gamma domain, coordinate and retained-density
graphs for the actual canonical normalized finite contraction object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {k a : ℕ}
variable {A : DefSet (M := M) S (k+1) a} {σ : Equiv.Perm (Fin (k+1))}

theorem normalized_volume_contraction_domain_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hC : GammaSetDefinable P (carrier C.target)) :
    GammaSetDefinable P {p : Point (M := M) 0 (canonicalNormalizedFiniteContraction hc C hF).obj.arity |
      p.2 ∈ (canonicalNormalizedFiniteContraction hc C hF).obj.domain.carrier} := C.gamma_normalized_domain hC

theorem normalized_volume_contraction_coordinates_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hPS : P.real ⊆ S) (hC : GammaSetDefinable P (carrier C.target)) :
    RVMapGamma (canonicalNormalizedFiniteContraction hc C hF).obj.volume P := by
  apply GammaGraphDefinable.congr (C.gammaNormalizedObject hPS hC).volume_graph
  intro p q
  exact ⟨fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩,
    fun ⟨u,hu,hq⟩ => ⟨⟨u.val,u.property⟩,hu,hq⟩⟩

theorem normalized_coordinate_density_volume_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : StandardContraction A σ) (hF : (canonicalRVObject hc C.contractionObject).volume.FiniteFibres)
    (hPS : P.real ⊆ S) (hC : GammaSetDefinable P (carrier C.target))
    (δ : Fin (canonicalNormalizedFiniteContraction hc C hF).obj.arity)
    (hδ : ∀ u : (canonicalNormalizedFiniteContraction hc C hF).obj.domain, u.val δ ≠ 0) :
    VolumeObjectGamma (coordinateDensityVolumeObject (canonicalNormalizedFiniteContraction hc C hF) δ hδ) P :=
  ⟨normalized_volume_contraction_coordinates_gamma hc C hF hPS hC,
    gamma_coordinate_density_graph _ (normalized_volume_contraction_domain_gamma hc C hF hC) δ (fun _ => rfl)⟩

end IntegrationInACVF.Section7
