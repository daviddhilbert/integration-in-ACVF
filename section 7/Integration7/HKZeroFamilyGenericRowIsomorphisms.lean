module

public import Integration7.HKZeroDensityGraphRowIsomorphisms
public import Integration7.GammaOrdinaryHeadFibreWitnesses
public import Integration7.HKAEZeroVolumeFunctions
public import Integration7.PureVFFormulaLoci

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! AE equality of weighted-zero functions gives exact-density point
isomorphisms at every generic full VF tuple on the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open SpecialTransformations.Section5 (Point GammaIso)
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}

theorem zero_family_ae_rows_eq_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (hAE : AEZeroVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (x : Fin (n+1) → SpecialTransformations.Milestone0.Transfer.VFType (M := M))
    (hx : AlgebraicIndependent (vfParameterField (C.base : Set M)) x) :
    rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (F.rowInContext x) =
      rvVolumeBlowupClass hc (vfParameterVolumeContext C x) (n := 0) (G.rowInContext x) := by
  obtain ⟨E,hE,hRows⟩ := hAE
  exact hRows x (fun h => pure_vf_small_has_no_independent hc E hE ⟨x,h⟩ hx)

theorem zero_family_ae_density_point_iso_at_generic
    (hc : CanonicalStructure.IsCanonical (M := M)) (Ξ : Set (Values.Gamma (M := M)))
    (F : ZeroVFVolumeFamily C (n+1) a) (G : ZeroVFVolumeFamily C (n+1) b)
    (hAE : AEZeroVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (x : Fin (n+1) → SpecialTransformations.Milestone0.Transfer.VFType (M := M))
    (hx : AlgebraicIndependent (vfParameterField (C.base : Set M)) x) :
    ∃ e : GammaIso (⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),Ξ⟩ : Base (M := M))
      {q : Point (M := M) 0 (a+1) | (x,q.2) ∈
        SpecialTransformations.Section5.carrier (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain)}
      {q : Point (M := M) 0 (b+1) | (x,q.2) ∈
        SpecialTransformations.Section5.carrier (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain)},
      ∀ u, u.val.2 (Fin.last a) = (e.equiv u).val.2 (Fin.last b) := by
  obtain ⟨e,he⟩ := zero_density_graph_row_iso_of_class_eq hc F G x
    (zero_family_ae_rows_eq_at_generic hc F G hAE x hx)
  let f := e.congr
    (vf_parameter_empty_fibre_domain (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) x)
    (vf_parameter_empty_fibre_domain (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain) x)
  refine ⟨⟨f.equiv,f.graph.mono (Set.Subset.refl _) (Set.empty_subset Ξ)⟩,?_⟩
  exact weighted_point_iso_congr_density e
    (vf_parameter_empty_fibre_domain (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain) x)
    (vf_parameter_empty_fibre_domain (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain) x)
    (Fin.last a) (Fin.last b) he

end IntegrationInACVF.Section7.HK
