import Integration7.ElementaryVolumeProducts
import Integration7.VolumeProductDistributivity
import Integration7.RVVolumeProducts
import Integration7.VolumeBlowupEquivalence

/-! Left multiplication preserves genuine positive common blowups.
The distinguished coordinate remains last throughout each actual chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k n : ℕ}

def VolumeBlowup.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U V) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) n) :
    VolumeBlowup (R.prod U) (R.prod V) where
  locus := R.prod b.locus
  complement := R.prod b.complement
  blownLocus := R.prod b.blownLocus
  elementary := b.elementary.product_left R
  sourceIso := ((RVVolumeIso.refl hc C R).prod hc C b.sourceIso).trans hc C
    (volumeProductRightDistribIso hc C R b.locus b.complement)
  targetIso := ((RVVolumeIso.refl hc C R).prod hc C b.targetIso).trans hc C
    (volumeProductRightDistribIso hc C R b.blownLocus b.complement)

theorem IteratedVolumeBlowup.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {d : ℕ}
    (h : IteratedVolumeBlowup d U V)
    (R : PositiveRVVolumeObject (M := M) (C.base : Set M) n) :
    IteratedVolumeBlowup d (R.prod U) (R.prod V) := by
  induction h with
  | refl U => exact .refl _
  | step b h ih => exact .step ⟨b.some.product_left hc C R⟩ ih

theorem VolumeBlowupEquivalent.product_left
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V)
    (R : PositiveRVVolumeObject (M := M) (C.base : Set M) n) :
    VolumeBlowupEquivalent (R.prod U) (R.prod V) := by
  obtain ⟨a,b,U',V',hU,hV,⟨e⟩⟩ := h
  exact ⟨a,b,R.prod U',R.prod V',hU.product_left hc C R,hV.product_left hc C R,
    ⟨(RVVolumeIso.refl hc C R).prod hc C e⟩⟩

end IntegrationInACVF.Section7
