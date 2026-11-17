module

public import Integration7.HKWeightedZeroDistributivity
public import Integration7.HKMixedVolumeIsomorphisms
public import Integration7.VolumeBlowupEquivalence

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Full blowup chains commute with arbitrary weighted degree-zero factors. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def weightedZeroBlowup (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U V) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VolumeBlowup (zeroProduct Z U) (zeroProduct Z V) where
  locus := zeroProduct Z b.locus
  complement := zeroProduct Z b.complement
  blownLocus := zeroProduct Z b.blownLocus
  elementary := weightedZeroElementary b.elementary Z
  sourceIso := (zeroProductIso hc C (ZeroRVVolumeIso.refl Z) b.sourceIso).trans hc C
    (volumeZeroProductRightDistribIso hc C Z b.locus b.complement)
  targetIso := (zeroProductIso hc C (ZeroRVVolumeIso.refl Z) b.targetIso).trans hc C
    (volumeZeroProductRightDistribIso hc C Z b.blownLocus b.complement)

theorem weightedZeroIterated (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {d : ℕ}
    (h : IteratedVolumeBlowup d U V) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    IteratedVolumeBlowup d (zeroProduct Z U) (zeroProduct Z V) := by
  induction h with
  | refl U => exact .refl _
  | step b h ih => exact .step ⟨weightedZeroBlowup hc C b.some Z⟩ ih

theorem weightedZeroEquivalent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VolumeBlowupEquivalent (zeroProduct Z U) (zeroProduct Z V) := by
  obtain ⟨a,b,U',V',hU,hV,⟨e⟩⟩ := h
  exact ⟨a,b,zeroProduct Z U',zeroProduct Z V',weightedZeroIterated hc C hU Z,
    weightedZeroIterated hc C hV Z,⟨zeroProductIso hc C (ZeroRVVolumeIso.refl Z) e⟩⟩

theorem weightedPositiveZeroEquivalent
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (Z : ZeroRVVolumeObject (M := M) (C.base : Set M)) :
    VolumeBlowupEquivalent (positiveZeroProduct U Z) (positiveZeroProduct V Z) :=
  ((VolumeBlowupEquivalent.of_iso C (mixedProductSwapIso hc C U Z)).trans hc C
    (weightedZeroEquivalent hc C h Z)).trans hc C
      (VolumeBlowupEquivalent.of_iso C ((mixedProductSwapIso hc C V Z).symm hc C))

theorem weightedZeroProdEquivalent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (g : ZeroRVVolumeIso Z T) (h : VolumeBlowupEquivalent U V) :
    VolumeBlowupEquivalent (zeroProduct Z U) (zeroProduct T V) :=
  (VolumeBlowupEquivalent.of_iso C (zeroProductIso hc C g (RVVolumeIso.refl hc C U))).trans hc C
    (weightedZeroEquivalent hc C h T)

theorem weightedProdZeroEquivalent (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : ZeroRVVolumeObject (M := M) (C.base : Set M)}
    (h : VolumeBlowupEquivalent U V) (g : ZeroRVVolumeIso Z T) :
    VolumeBlowupEquivalent (positiveZeroProduct U Z) (positiveZeroProduct V T) :=
  (weightedPositiveZeroEquivalent hc C h Z).trans hc C
    (VolumeBlowupEquivalent.of_iso C (positiveZeroProductIso hc C (RVVolumeIso.refl hc C V) g))

end IntegrationInACVF.Section7.HK
