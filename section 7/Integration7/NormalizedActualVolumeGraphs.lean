module

public import Integration7.NormalizedActualRVObjects
public import Integration7.GammaVolumeAlgebraicCenters
public import IntegrationSection6.FiniteGammaObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Original-Gamma coordinate graphs and algebraic centers carry over
to the literal normalized presentation of an actual volume object. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def normalizedActualVolumeGammaObject (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) (hU : VolumeObjectGamma U B) (hBS : B.real ⊆ S) :
    FiniteRV.GammaObjectAt B S (k+1) where
  object := normalizedActualFiniteRVObject hc U.underlying
  real_contains := hBS
  domain_graph := hU.coordinates.domain
  volume_graph := hU.coordinates

theorem normalized_actual_volume_gamma_admissible
    (hc : CanonicalStructure.IsCanonical (M := M))
    (U : PositiveRVVolumeObject (M := M) S k) (hU : VolumeObjectGamma U B) (hBS : B.real ⊆ S)
    (hAd : BlowupAdmissible U) (hCenter : GammaBlowupCenter U B) :
    GammaAdmissible
      (normalizedActualVolumeGammaObject hc U hU hBS).toGamma.toGammaRVObject (Fin.last k) := by
  constructor
  · intro u
    exact (rv_nonzero_iff_raw _).mp (hAd.nonzero ⟨u.val,u.property⟩)
  · intro u
    exact hCenter ⟨u.val,u.property⟩

end IntegrationInACVF.Section7
