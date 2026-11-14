import Integration7.GammaVolumeGraphPresentations
import Integration7.GammaVolumeSchemaDensityGraphs

/-! Every valid volume-schema row gives an actual finite real volume
presentation with its original-Gamma domain, coordinate and density graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.realize (F : GammaRVVolumeSchema B p a k sp)
    (z : Fin p → M) (hz : F.valid z) :
    Nonempty (GammaVolumeGraphPresentation ⟨B.real ∪ Set.range z,B.gamma⟩ a (k+1)
      (F.object.rowDomain z) (F.object.rowVolume z) (F.rowDensity z)) := by
  obtain ⟨P⟩ := F.object.realize z hz.1
  exact exists_gammaVolumeGraphPresentation P (F.rowDensity_graph z hz)
    (F.rowDensity_unique z hz) (fun x y => F.rowDensity_support z hz x y)
    (fun x y => F.rowDensity_nonzero z x y)

end IntegrationInACVF.Section7
