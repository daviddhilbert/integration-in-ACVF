import Integration7.VolumeEmbeddedImages
import Integration7.EssentialVolumeRestriction
import Integration7.RVVolumeInverse

/-! Removing the left essential summand leaves the right volume class,
including any discarded degenerate labels in the ambient complement. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def volumeCoprodLeftComplementIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso
      ((U.coprod V).restrict
        ((U.coprod V).underlying.obj.domain.sdiff (coprodEssentialLeftMap U V).image) Set.sdiff_subset) V := by
  let T := U.coprod V
  let A := (coprodEssentialLeftMap U V).image
  let B := (coprodEssentialRightMap U V).image
  let D := T.restrict (T.underlying.obj.domain.sdiff A) Set.sdiff_subset
  have hBD : B.carrier ⊆ D.underlying.obj.domain.carrier := by
    rintro x ⟨v, rfl⟩
    refine ⟨rvEssentialLabels_subset T.underlying.obj (coprodEssentialRightMap U V v).property, ?_⟩
    rintro ⟨u, he⟩
    apply Set.disjoint_left.mp (rvTaggedImages_disjoint U.underlying.obj.domain V.underlying.obj.domain)
    · exact ⟨⟨u.val, rvEssentialLabels_subset U.underlying.obj u.property⟩, he⟩
    · exact ⟨⟨v.val, rvEssentialLabels_subset V.underlying.obj v.property⟩, rfl⟩
  have hess : D.essential.obj.domain.carrier ⊆ B.carrier := by
    intro x hx
    let w : T.essential.obj.domain :=
      ⟨x, essentialRestriction_subset T _ Set.sdiff_subset hx⟩
    rcases coprodEssential_cover U V w with ⟨u, hu⟩ | ⟨v, hv⟩
    · exact False.elim (hx.1.2 ⟨u, congrArg (fun p : T.essential.obj.domain => p.val) hu⟩)
    · exact ⟨v, congrArg (fun p : T.essential.obj.domain => p.val) hv⟩
  have e : RVVolumeIso (T.restrict B (essentialMapImage_subset (coprodEssentialRightMap U V))) D :=
    volumeIsoOfContainingEssentialRestriction hc C D B hBD hess
  exact (e.symm hc C).trans hc C ((volumeCoprodRightImageIso hc C U V).symm hc C)

end IntegrationInACVF.Section7
