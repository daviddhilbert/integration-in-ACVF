module

public import Integration7.IndexedVolumeDensityLabels
public import Integration7.GammaVolumeSliceDensityAssembly

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! An indexed presentation whose density is a retained label is
volume isomorphic to the actual canonical coordinate-density object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ}
variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def indexedVolumeCoordinateDensityIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (F : GammaRVVolumeSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R) (P : F.IndexedPresentation BP)
    (hPC : P.finite.codes ⊆ (C.base : Set M)) (δ : Fin a)
    (hDensity : ∀ s ∈ T, ∀ r w, F.rowDensity (rvValues s) r w ↔
      r ∈ F.object.rowDomain (rvValues s) ∧ w 0 = r δ) :
    RVVolumeIso (P.inContext hc C hPC).toObject
      (gammaCoordinateDensityObject (e := d) (k := k) hc C P.finite.toGamma hPC
        (Fin.natAdd p δ) (indexed_volume_presentation_density_nonzero F BP P δ hDensity)) := by
  let A := (P.inContext hc C hPC).toObject
  let V := gammaCoordinateDensityObject (e := d) (k := k) hc C P.finite.toGamma hPC
    (Fin.natAdd p δ) (indexed_volume_presentation_density_nonzero F BP P δ hDensity)
  let f : Map A.underlying.obj.domain V.underlying.obj.domain := Map.inclusion (fun _ h => h)
  have hf : Function.Bijective f := ⟨fun _ _ h => Subtype.ext (congrArg Subtype.val h),
    fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩
  have hcoord : ∀ u, V.underlying.obj.value (f u) = A.underlying.obj.value u := fun _ => rfl
  exact RVVolumeIso.of_preserving_coordinates_full hc C
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)) hcoord (fun u =>
      (indexed_volume_presentation_density_label F BP P δ hDensity ⟨u.val,u.property⟩).symm)

end IntegrationInACVF.Section7
