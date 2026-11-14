import Integration7.VolumeCoproductAssociativity
import Integration7.GradedVolumeProducts
import Integration7.RVVolumeInverse

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveRVVolumeObject.empty (S : Set M) (k : ℕ) : PositiveRVVolumeObject (M := M) S k :=
  ⟨rvFiniteEmpty S (k + 1), VolumeForm.one _⟩

def volumeCoprodEmptyEmbedding
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso U (U.coprod (.empty (C.base : Set M) k)) := by
  let E := PositiveRVVolumeObject.empty (M := M) (C.base : Set M) k
  let F : Map U.underlying.obj.domain (U.coprod E).underlying.obj.domain :=
    rvCoprodLeftMap U.underlying.obj E.underlying.obj
  have hF : Function.Bijective F := by
    constructor
    · intro a b he
      exact Subtype.ext (rvLeftTag_injective E.underlying.obj.arity
        (congrArg (fun w : (U.coprod E).underlying.obj.domain => w.val) he))
    · intro w
      rcases volumeCoprod_cases U E w with ⟨u, hu⟩ | ⟨v, hv⟩
      · exact ⟨u, hu⟩
      · exact False.elim v.property
  let e : U.underlying ≅ (U.coprod E).underlying := rvFiniteIsoOfAmbient
    (rvIsoOfVolumePreservingBijection F hF (fun u => rvCoprod_value_left U.underlying.obj E.underlying.obj u))
  apply RVVolumeIso.of_preserving_coordinates_full hc C e
  · intro u
    exact rvCoprod_value_left U.underlying.obj E.underlying.obj u
  · intro u
    exact coprod_density_left U E u

def volumeCoprodRightUnit
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.coprod (.empty (C.base : Set M) k)) U :=
  (volumeCoprodEmptyEmbedding hc C U).symm hc C

def volumeCoprodLeftUnit
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso ((PositiveRVVolumeObject.empty (C.base : Set M) k).coprod U) U :=
  (volumeCoprodSwap hc C _ U).trans hc C (volumeCoprodRightUnit hc C U)

end IntegrationInACVF.Section7
