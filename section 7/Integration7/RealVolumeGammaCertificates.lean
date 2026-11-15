import Integration7.TermContextGammaGraphs
import Integration7.GammaVolumeAlgebraicCenters
import Integration7.GammaVolumeObjectGraphs

/-! Actual real-definable volume objects and admissible centers have
their full Gamma certificates over that same real base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

theorem volume_object_gamma_over_real_base (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VolumeObjectGamma U (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) := by
  have hBase : (C.base : Set M) = (Substructure.closure LRV (C.base : Set M) : Set M) := by simp
  exact ⟨gammaGraph_of_termContext hc C _ hBase U.underlying.obj.volume.graph_definable,
    gammaGraph_of_termContext hc C _ hBase U.form.map.graph_definable⟩

theorem blowup_center_gamma_over_real_base (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M)))
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hAd : BlowupAdmissible U) :
    GammaBlowupCenter U (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) := by
  intro u
  obtain ⟨A,hA,hfin,hu⟩ := hAd.algebraic u
  exact ⟨A,real_definableAtBase _ .rv _ hA,hfin,hu⟩

end IntegrationInACVF.Section7
