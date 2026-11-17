module

public import Integration7.GammaElementaryBlowupIsomorphisms
public import Integration7.GammaCanonicalElementaryGraphs

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The canonical elementary comparison retains the original Gamma
graphs of coordinates, densities and the resulting volume isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem canonical_gamma_elementary_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : FiniteRV.GammaObjectAt B (C.base : Set M) (k+1))
    (ω : VolumeForm (canonicalFiniteRVObject hc U.object).obj.domain)
    (π : VolumeForm (canonicalFiniteRVObject hc V.object).obj.domain)
    (hU : GammaAdmissible U.toGamma.toGammaRVObject (Fin.last k))
    (hV : GammaAdmissible V.toGamma.toGammaRVObject (Fin.last k))
    (hω : RVMapGamma ω.map B) (hπ : RVMapGamma π.map B)
    (f : RVVolumeIso
      (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
      (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k))
    (hf : f.GammaDefinable B) :
    ∃ e : RVVolumeIso
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc U.object,ω⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C U ω hU))
      (elementaryVolumeObject C
        (⟨canonicalFiniteRVObject hc V.object,π⟩ : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
        (canonicalGammaElementaryAdmissible hc C V π hV)), e.GammaDefinable B := by
  apply exists_gamma_elementaryBlowupIso hc C B f
    (elementaryVolumeBlowup C _ (canonicalGammaElementaryAdmissible hc C U ω hU))
    (elementaryVolumeBlowup C _ (canonicalGammaElementaryAdmissible hc C V π hV))
    (canonical_gamma_object_volume_graph hc U) (canonical_gamma_object_volume_graph hc V) hω hπ hf
  · exact gamma_canonical_packed_elementary_chart hc C B _ _
      (gamma_canonical_elementary_coordinates hc C U ω hU)
  · exact gamma_canonical_packed_elementary_chart hc C B _ _
      (gamma_canonical_elementary_coordinates hc C V π hV)

end IntegrationInACVF.Section7
