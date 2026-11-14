import Integration7.EssentialVolumeCoproduct
import Integration7.VolumeRelabeling
import Integration7.NondegenerateFiniteIso

/-! Coordinate- and density-preserving essential embeddings identify an
object with its actual definable image. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

theorem essentialMapImage_subset {U V : PositiveRVVolumeObject (M := M) S k}
    (i : Map U.essential.obj.domain V.essential.obj.domain) :
    i.image.carrier ⊆ V.underlying.obj.domain.carrier := by
  rintro x ⟨u, rfl⟩
  exact rvEssentialLabels_subset V.underlying.obj (i u).property

def volumeIsoOfEssentialEmbedding
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (i : Map U.essential.obj.domain V.essential.obj.domain) (hi : Function.Injective i)
    (hcoord : ∀ u, V.essential.obj.value (i u) = U.essential.obj.value u)
    (hφ : ∀ u, V.essentialForm.value (i u) = U.essentialForm.value u) :
    RVVolumeIso U (V.restrict i.image (essentialMapImage_subset i)) := by
  let R := V.restrict i.image (essentialMapImage_subset i)
  have ht (u : U.essential.obj.domain) : (i.toImage u).val ∈ R.essential.obj.domain.carrier := by
    apply (mem_rvEssentialLabels R.underlying.obj (i.toImage u)).mpr
    exact V.essential_nonzero (i u)
  let F : Map U.essential.obj.domain R.essential.obj.domain := i.toImage.corestrict ht
  have hF : Function.Bijective F := by
    constructor
    · intro a b h
      exact hi (Subtype.ext (congrArg (fun r : R.essential.obj.domain => r.val) h))
    · intro r
      obtain ⟨u, hu⟩ := r.property.1
      exact ⟨u, Subtype.ext hu⟩
  let e : U.essential ≅ R.essential :=
    finiteIsoOfNondegenerateBijection F hF U.essential_nonzero R.essential_nonzero
  apply RVVolumeIso.of_preserving_coordinates hc C e
  · intro u
    exact hcoord u
  · intro u
    exact hφ u

def volumeCoprodLeftImageIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso U ((U.coprod V).restrict (coprodEssentialLeftMap U V).image
      (essentialMapImage_subset (coprodEssentialLeftMap U V))) :=
  volumeIsoOfEssentialEmbedding hc C (coprodEssentialLeftMap U V)
    (coprodEssentialLeftMap_injective U V) (coprodEssentialLeftMap_coordinates U V)
    (coprodEssentialLeftMap_density U V)

def volumeCoprodRightImageIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso V ((U.coprod V).restrict (coprodEssentialRightMap U V).image
      (essentialMapImage_subset (coprodEssentialRightMap U V))) :=
  volumeIsoOfEssentialEmbedding hc C (coprodEssentialRightMap U V)
    (coprodEssentialRightMap_injective U V) (coprodEssentialRightMap_coordinates U V)
    (coprodEssentialRightMap_density U V)

end IntegrationInACVF.Section7
