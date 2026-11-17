module

public import Integration7.GammaVolumeCoproductAssociativity
public import Integration7.GammaVolumeCoproductCharts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Explicit coproduct rearrangements with original-Gamma certificates.
These supply concrete charts for the common-refinement square. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ} {B : Base (M := M)}

def volumeCoprodExchange (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.coprod (V.coprod W)) (V.coprod (U.coprod W)) :=
  (((volumeCoprodAssoc hc C U V W).symm hc C).trans hc C
    ((volumeCoprodSwap hc C U V).coprod hc C (RVVolumeIso.refl hc C W))).trans hc C
      (volumeCoprodAssoc hc C V U W)

theorem gamma_volume_coprod_exchange
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B) (hW : VolumeObjectGamma W B) :
    (volumeCoprodExchange hc C U V W).GammaDefinable B :=
  (((gamma_volume_coprod_assoc hc C hU hV hW).symm hc C B).trans hc C B
    ((gamma_volume_coprod_swap hc C hU hV).coprod hc C B (hW.identity_iso hc C))).trans hc C B
      (gamma_volume_coprod_assoc hc C hV hU hW)

def volumeCoprodReverseOuter (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V W E : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    RVVolumeIso (U.coprod ((V.coprod W).coprod E)) (W.coprod ((V.coprod U).coprod E)) :=
  (((((RVVolumeIso.refl hc C U).coprod hc C (volumeCoprodAssoc hc C V W E)).trans hc C
    (volumeCoprodExchange hc C U V (W.coprod E))).trans hc C
      ((RVVolumeIso.refl hc C V).coprod hc C (volumeCoprodExchange hc C U W E))).trans hc C
        (volumeCoprodExchange hc C V W (U.coprod E))).trans hc C
          ((RVVolumeIso.refl hc C W).coprod hc C ((volumeCoprodAssoc hc C V U E).symm hc C))

theorem gamma_volume_coprod_reverse_outer
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V W E : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (hU : VolumeObjectGamma U B) (hV : VolumeObjectGamma V B)
    (hW : VolumeObjectGamma W B) (hE : VolumeObjectGamma E B) :
    (volumeCoprodReverseOuter hc C U V W E).GammaDefinable B :=
  (((((hU.identity_iso hc C).coprod hc C B (gamma_volume_coprod_assoc hc C hV hW hE)).trans hc C B
    (gamma_volume_coprod_exchange hc C hU hV (hW.coprod hE))).trans hc C B
      ((hV.identity_iso hc C).coprod hc C B (gamma_volume_coprod_exchange hc C hU hW hE))).trans hc C B
        (gamma_volume_coprod_exchange hc C hV hW (hU.coprod hE))).trans hc C B
          ((hW.identity_iso hc C).coprod hc C B ((gamma_volume_coprod_assoc hc C hV hU hE).symm hc C B))

end IntegrationInACVF.Section7
