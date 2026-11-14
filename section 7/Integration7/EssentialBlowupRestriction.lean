import Integration7.EssentialVolumeRestriction
import Integration7.ElementaryBlowupRestriction
import Integration7.EssentialBlowupChart

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7.ElementaryBlowup

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def essentialSourceTargetIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W) :
    RVVolumeIso
      (W.restrict (b.sourcePreimage U.essential.obj.domain) (b.sourcePreimage_subset U.essential.obj.domain)) W :=
  volumeIsoOfContainingEssentialRestriction hc C W (b.sourcePreimage U.essential.obj.domain)
    (b.sourcePreimage_subset U.essential.obj.domain) (by
      intro x hx
      let w : W.underlying.obj.domain := ⟨x, rvEssentialLabels_subset W.underlying.obj hx⟩
      exact (b.mem_sourcePreimage U.essential.obj.domain w).mpr ((b.essential_mem_iff w).mp hx).1)

theorem exists_blowup_on_essential_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U W : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (b : ElementaryBlowup U W) :
    ∃ W' : PositiveRVVolumeObject (M := M) (C.base : Set M) k,
      Nonempty (ElementaryBlowup U.essentialCore W') ∧ Nonempty (RVVolumeIso W' W) :=
  ⟨_, ⟨b.restrict U.essential.obj.domain (rvEssentialLabels_subset U.underlying.obj)⟩,
    ⟨b.essentialSourceTargetIso hc C⟩⟩

end IntegrationInACVF.Section7.ElementaryBlowup
