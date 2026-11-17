module

public import Integration7.CanonicalActualRVIdentifications
public import Integration7.VolumeRelabeling

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An actual volume object has a canonical normalized presentation
whose identifying isomorphism fixes every label, coordinate and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def canonicalActualVolumeObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) : PositiveRVVolumeObject (M := M) S k :=
  ⟨canonicalFiniteRVObject hc (normalizedActualFiniteRVObject hc U.underlying),
    U.form.pullback (Map.inclusion (fun _ h => h))⟩

theorem actual_volume_canonical_presentation_iso (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    Nonempty (RVVolumeIso U (canonicalActualVolumeObject hc U)) := by
  let V := canonicalActualVolumeObject hc U
  let f : Map U.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := by
    constructor
    · intro u v h
      have hv := congrArg (fun w : V.underlying.obj.domain => w.val) h
      exact Subtype.ext hv
    · intro v
      exact ⟨⟨v.val,v.property⟩,rfl⟩
  let e := rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf (fun _ => rfl))
  exact ⟨RVVolumeIso.of_preserving_coordinates_full hc C e (fun _ => rfl) (fun _ => rfl)⟩

end IntegrationInACVF.Section7
