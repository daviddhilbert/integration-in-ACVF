import Integration7.GammaVolumeCoproductCoherence
import Integration7.VolumeRestrictionIdentifications

/-! Identity-on-label volume isomorphisms, including the existing nested
and carrier-equality restriction maps, retain their original Gamma graphs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 (Point GammaSetDefinable)

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

theorem gamma_volume_iso_of_label_identity {S : Set M}
    (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : PositiveRVVolumeObject (M := M) S k} (e : RVVolumeIso U V)
    (hU : VolumeObjectGamma U B) (ha : U.underlying.obj.arity = V.underlying.obj.arity)
    (he : ∀ u, (finiteIsoMap e.iso u).val = u.val ∘ Fin.cast ha.symm) :
    e.GammaDefinable B := by
  exact gamma_real_rv_map_graph hc B (finiteIsoMap e.iso)
    (rvCoordinateSelectMap B.real (Fin.cast ha.symm))
    (gamma_essential_volume_domain U hU.coordinates) he

theorem gamma_volume_restriction_carrier_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A D : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier)
    (hD : D.carrier ⊆ U.underlying.obj.domain.carrier) (he : A.carrier = D.carrier)
    (hΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier}) :
    (volumeRestrictionCarrierIso hc C U A D hA hD he).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ (hU.restrict A hA hΓ) rfl (fun _ => rfl)

theorem gamma_volume_restriction_trans_iso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) (hU : VolumeObjectGamma U B)
    (A D : DefSet (rawRVSpace (M := M) U.underlying.obj.arity) (C.base : Set M))
    (hA : A.carrier ⊆ U.underlying.obj.domain.carrier) (hDA : D.carrier ⊆ A.carrier)
    (hAΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ A.carrier})
    (hDΓ : GammaSetDefinable B {p : Point (M := M) 0 U.underlying.obj.arity | p.2 ∈ D.carrier}) :
    (volumeRestrictionTransIso hc C U A D hA hDA).GammaDefinable B :=
  gamma_volume_iso_of_label_identity hc _ ((hU.restrict A hA hAΓ).restrict D hDA hDΓ) rfl (fun _ => rfl)

end IntegrationInACVF.Section7
