module

public import Integration7.GammaVolumeObjectGraphs
public import Integration7.GammaVolumeIsoGraphOperations
public import Integration7.VolumeSubobjects

@[expose] public section

/-! Images of Gamma essential subobjects and the actual restricted
volume isomorphism retain the original Gamma base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_subobject_image {S : Set M}
    {U V : PositiveRVVolumeObject (M := M) S k} (f : RVVolumeIso U V)
    (hf : f.GammaDefinable B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) S)
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    GammaSetDefinable B {q : Point (M := M) 0 V.underlying.obj.arity |
      q.2 ∈ (volumeSubobjectImage f A hA).carrier} := by
  have hMap : RVMapGamma ((finiteIsoMap f.iso).restrict hA) B :=
    (show RVMapGamma (finiteIsoMap f.iso) B from hf).restrict hA hΓ
  have hImage : RVMapGamma ((finiteIsoMap f.iso).restrict hA).toImage B := hMap.congr (fun _ => rfl)
  exact hImage.range (by rintro ⟨_,a,rfl⟩; exact ⟨a,rfl⟩)

theorem gamma_volume_subobject_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (f : RVVolumeIso U V)
    (hf : f.GammaDefinable B) (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (f.subobjectImage hc C A hA).GammaDefinable B := by
  let L := U.restrict A (hA.trans (rvEssentialLabels_subset U.underlying.obj))
  have hLE := gamma_essential_volume_domain L
    (hU.restrict A (hA.trans (rvEssentialLabels_subset U.underlying.obj)) hΓ).coordinates
  have hMap := (show RVMapGamma (finiteIsoMap f.iso) B from hf).restrict
    ((rvEssentialLabels_subset L.underlying.obj).trans hA) hLE
  exact hMap.congr (fun _ => rfl)

end IntegrationInACVF.Section7
