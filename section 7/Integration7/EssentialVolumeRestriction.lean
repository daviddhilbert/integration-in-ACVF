import Integration7.NondegenerateFiniteIso
import Integration7.VolumeRelabeling

/-! Restricting to a definable set containing every essential label does
not change the volume-isomorphism class. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem essentialRestriction_subset (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) :
    (U.restrict A hA).essential.obj.domain.carrier ⊆ U.essential.obj.domain.carrier := by
  intro x hx
  exact (mem_rvEssentialLabels U.underlying.obj ⟨x, hA hx.1⟩).mpr
    ((U.restrict A hA).essential_nonzero ⟨x, hx⟩)

def essentialRestrictionUnderlyingIso (U : PositiveRVVolumeObject (M := M) S k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hess : U.essential.obj.domain.carrier ⊆ A.carrier) :
    (U.restrict A hA).essential ≅ U.essential := by
  let L := U.restrict A hA
  have hsub : L.essential.obj.domain.carrier ⊆ U.essential.obj.domain.carrier := by
    intro x hx
    apply (mem_rvEssentialLabels U.underlying.obj ⟨x, hA hx.1⟩).mpr
    exact L.essential_nonzero ⟨x, hx⟩
  let F : Map L.essential.obj.domain U.essential.obj.domain := Map.inclusion hsub
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (congrArg (fun u : U.essential.obj.domain => u.val) he)
    · intro u
      have hu : u.val ∈ L.essential.obj.domain.carrier :=
        (mem_rvEssentialLabels L.underlying.obj ⟨u.val, hess u.property⟩).mpr (U.essential_nonzero u)
      exact ⟨⟨u.val, hu⟩, rfl⟩
  exact finiteIsoOfNondegenerateBijection
    (U := L.essential) (V := U.essential) F hF L.essential_nonzero U.essential_nonzero

def volumeIsoOfContainingEssentialRestriction
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hess : U.essential.obj.domain.carrier ⊆ A.carrier) : RVVolumeIso (U.restrict A hA) U :=
  RVVolumeIso.of_preserving_coordinates hc C (essentialRestrictionUnderlyingIso U A hA hess)
    (fun _ => rfl) (fun _ => rfl)

def PositiveRVVolumeObject.essentialCore (U : PositiveRVVolumeObject (M := M) S k) :
    PositiveRVVolumeObject (M := M) S k :=
  U.restrict U.essential.obj.domain (rvEssentialLabels_subset U.underlying.obj)

def essentialCoreIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : RVVolumeIso U.essentialCore U :=
  volumeIsoOfContainingEssentialRestriction hc C U U.essential.obj.domain
    (rvEssentialLabels_subset U.underlying.obj) (Set.Subset.refl _)

end IntegrationInACVF.Section7
