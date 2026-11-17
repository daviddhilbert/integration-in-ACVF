module

public import Integration7.GammaVolumeSubobjects
public import Integration7.VolumeComplementImages

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual isomorphism on complementary volume pieces retains its
original-Gamma graph. Both degeneracy and the exact image cut are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable gammaLogicInput)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_complement_image_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} (f : RVVolumeIso U V)
    (hf : f.GammaDefinable B) (hU : VolumeObjectGamma U B)
    (A : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.essential.obj.domain.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (f.complementImage hc C A hA).GammaDefinable B := by
  let D := U.underlying.obj.domain.sdiff A
  let L := U.restrict D Set.sdiff_subset
  have hD := (gammaLogicInput B).sdiff hU.coordinates.domain hΓ
  have hLE := gamma_essential_volume_domain L (hU.restrict D Set.sdiff_subset hD).coordinates
  have hMap := (show RVMapGamma (finiteIsoMap f.iso) B from hf).restrict
    (essentialRestriction_subset U D Set.sdiff_subset) hLE
  exact hMap.congr (fun _ => rfl)

end IntegrationInACVF.Section7
