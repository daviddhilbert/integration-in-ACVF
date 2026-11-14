import Integration7.VolumeDensityRescaling
import Integration7.VolumeBlowupEquivalence
import Section4.RVReindexing
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {a b : ℕ}

def PositiveRVVolumeObject.cast (U : PositiveRVVolumeObject (M := M) S a) (h : a=b) :
    PositiveRVVolumeObject (M := M) S b := h ▸ U

def PositiveRVVolumeObject.reindexDegree (U : PositiveRVVolumeObject (M := M) S b) (h : a=b) :
    PositiveRVVolumeObject (M := M) S a where
  underlying := ⟨U.underlying.obj.reindexVolume (finCongr (congrArg Nat.succ h)),
    (Map.finiteFibres_of_injective (rvReindexMap_bijective S (finCongr (congrArg Nat.succ h))).1).comp
      U.underlying.property⟩
  form := U.form

def volumeCastReindexIso (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U : PositiveRVVolumeObject (M := M) (C.base : Set M) b) (h : a=b) :
    RVVolumeIso (U.reindexDegree h) (U.cast h.symm) := by
  cases h
  apply RVVolumeIso.of_preserving_coordinates_full hc C (U := U.reindexDegree rfl) (V := U)
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection
      (U := (U.reindexDegree rfl).underlying.obj) (V := U.underlying.obj)
      (Map.id U.underlying.obj.domain) Function.bijective_id (fun _ => rfl)))
  · intro _
    rfl
  · intro _
    rfl

def RVVolumeIso.cast {U V : PositiveRVVolumeObject (M := M) S a} (f : RVVolumeIso U V) (h : a=b) :
    RVVolumeIso (U.cast h) (V.cast h) := by
  cases h
  exact f

theorem IteratedVolumeBlowup.cast {d : ℕ} {U V : PositiveRVVolumeObject (M := M) S a}
    (g : IteratedVolumeBlowup d U V) (h : a=b) : IteratedVolumeBlowup d (U.cast h) (V.cast h) := by
  cases h
  exact g

theorem VolumeBlowupEquivalent.cast {U V : PositiveRVVolumeObject (M := M) S a}
    (g : VolumeBlowupEquivalent U V) (h : a=b) : VolumeBlowupEquivalent (U.cast h) (V.cast h) := by
  cases h
  exact g
end IntegrationInACVF.Section7
