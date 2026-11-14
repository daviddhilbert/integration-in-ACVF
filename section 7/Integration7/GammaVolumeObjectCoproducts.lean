import Integration7.GammaVolumeObjectGraphs
import Integration7.GammaTaggedRVMapGraphs
import Integration7.VolumeCoproduct

/-! Actual volume coproducts retain original-Gamma coordinates and
densities, with no choice of a new presentation or parameter base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

theorem VolumeObjectGamma.coprod {U V : PositiveRVVolumeObject (M := M) S k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) :
    VolumeObjectGamma (U.coprod V) B := by
  constructor
  · exact gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _ _ _
      hU.coordinates hV.coordinates
      (fun u => rvCoprod_value_left U.underlying.obj V.underlying.obj u)
      (fun v => rvCoprod_value_right U.underlying.obj V.underlying.obj v)
  · apply gamma_tagged_rv_map_graph U.underlying.obj V.underlying.obj _ _ _ hU.density hV.density
    · intro u
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact coprod_density_left U V u
    · intro v
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact coprod_density_right U V v

end IntegrationInACVF.Section7
