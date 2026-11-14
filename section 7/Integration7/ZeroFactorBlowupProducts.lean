import Integration7.ElementaryZeroVolumeProducts
import Integration7.ZeroFactorVolumeDistributivity
import Integration7.ZeroFactorVolumeIsomorphisms
import Integration7.VolumeBlowupEquivalence

/-! Multiplicative compatibility with ordinary RV[0] factors uses
their actual finite-volume maps, without adding or cancelling a point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}

def VolumeBlowup.zero_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U V) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VolumeBlowup (PositiveRVVolumeObject.zero_prod Z U) (.zero_prod Z V) where
  locus := .zero_prod Z b.locus
  complement := .zero_prod Z b.complement
  blownLocus := .zero_prod Z b.blownLocus
  elementary := b.elementary.zero_product Z
  sourceIso := (RVVolumeIso.zero_prod hc C (Iso.refl Z) b.sourceIso).trans hc C
    (volumeZeroProductRightDistribIso hc C Z b.locus b.complement)
  targetIso := (RVVolumeIso.zero_prod hc C (Iso.refl Z) b.targetIso).trans hc C
    (volumeZeroProductRightDistribIso hc C Z b.blownLocus b.complement)

theorem IteratedVolumeBlowup.zero_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {d : ℕ}
    (h : IteratedVolumeBlowup d U V) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    IteratedVolumeBlowup d (PositiveRVVolumeObject.zero_prod Z U) (.zero_prod Z V) := by
  induction h with
  | refl U => exact .refl _
  | step b h ih => exact .step ⟨b.some.zero_product hc C Z⟩ ih

theorem VolumeBlowupEquivalent.zero_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VolumeBlowupEquivalent (PositiveRVVolumeObject.zero_prod Z U) (.zero_prod Z V) := by
  obtain ⟨a,b,U',V',hU,hV,⟨e⟩⟩ := h
  exact ⟨a,b,.zero_prod Z U',.zero_prod Z V',hU.zero_product hc C Z,hV.zero_product hc C Z,
    ⟨RVVolumeIso.zero_prod hc C (Iso.refl Z) e⟩⟩

theorem VolumeBlowupEquivalent.product_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (Z : RVFiniteObject (M := M) (C.base : Set M) 0) :
    VolumeBlowupEquivalent (U.prod_zero Z) (V.prod_zero Z) :=
  ((VolumeBlowupEquivalent.of_iso C (volumeZeroProductSwapIso hc C U Z)).trans hc C
    (h.zero_product hc C Z)).trans hc C
      (VolumeBlowupEquivalent.of_iso C ((volumeZeroProductSwapIso hc C V Z).symm hc C))

theorem VolumeBlowupEquivalent.zero_prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : RVFiniteObject (M := M) (C.base : Set M) 0}
    (g : Z ≅ T) (h : VolumeBlowupEquivalent U V) :
    VolumeBlowupEquivalent (PositiveRVVolumeObject.zero_prod Z U) (.zero_prod T V) :=
  (VolumeBlowupEquivalent.of_iso C (RVVolumeIso.zero_prod hc C g (RVVolumeIso.refl hc C U))).trans hc C
    (h.zero_product hc C T)

theorem VolumeBlowupEquivalent.prod_zero
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {Z T : RVFiniteObject (M := M) (C.base : Set M) 0}
    (h : VolumeBlowupEquivalent U V) (g : Z ≅ T) :
    VolumeBlowupEquivalent (U.prod_zero Z) (V.prod_zero T) :=
  (h.product_zero hc C Z).trans hc C
    (VolumeBlowupEquivalent.of_iso C ((RVVolumeIso.refl hc C V).prod_zero hc C g))

end IntegrationInACVF.Section7
