import Integration7.GammaVolumeElementaryFormulas
import Integration7.GammaFunctionalRowRecognition

/-! Pulling a density back along the elementary label projection gives
a unique nonzero density on the exact elementary source domain. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a k : ℕ} {sp : Fin p → SortTag}

theorem GammaRVVolumeSchema.elementary_rowDensity_unique
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hF : F.valid z)
    (w : F.elementaryFormula.object.rowDomain z) :
    ∃! ω : Fin 1 → CanonicalRV.RVSort M, F.elementaryFormula.rowDensity z w.val ω := by
  have hx : w.val ∘ Fin.castAdd 1 ∈ F.object.rowDomain z := by
    have h : Fin.append z (rvValues w.val) ∘ rawElementaryHead p a ∈ F.object.domain := w.property.1
    rw [rawElementaryHead_append] at h
    exact h
  obtain ⟨ω,hω,hu⟩ := F.rowDensity_unique z hF ⟨w.val ∘ Fin.castAdd 1,hx⟩
  refine ⟨ω,(F.elementary_rowDensity z hF.1.1 w.val ω).mpr ⟨hω,w.property⟩,?_⟩
  intro ω' hω'
  exact hu ω' ((F.elementary_rowDensity z hF.1.1 w.val ω').mp hω').1

theorem GammaRVVolumeSchema.elementary_density_valid
    (F : GammaRVVolumeSchema B p a k sp) (z : Fin p → M) (hF : F.valid z) :
    functionMapRowValid sp F.elementaryFormula.object.domain F.elementaryFormula.density z :=
  functionMapRowValid_of_typed F.elementaryFormula.object.domain_definable F.elementaryFormula.density_definable
    z hF.1.1 (fun w hw => F.elementary_rowDensity_unique z hF ⟨w,hw⟩)
    (fun w ω h => ((F.elementary_rowDensity z hF.1.1 w ω).mp h).2)

end IntegrationInACVF.Section7
