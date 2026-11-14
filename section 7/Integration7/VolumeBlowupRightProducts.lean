import Integration7.VolumeBlowupProducts
import Integration7.VolumeBlowupRescaling
import Integration7.SignedVolumeProductSwap

/-! Right multiplication uses the genuine signed block swap. Its sign
is removed by rescaling both blowup chains by the same named constant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section4.ResiduePurity

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem VolumeBlowupEquivalent.reindexDegree
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {a b : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) b}
    (g : VolumeBlowupEquivalent U V) (h : a=b) :
    VolumeBlowupEquivalent (U.reindexDegree h) (V.reindexDegree h) :=
  ((VolumeBlowupEquivalent.of_iso C (volumeCastReindexIso hc C U h)).trans hc C
    (g.cast h.symm)).trans hc C
      (VolumeBlowupEquivalent.of_iso C ((volumeCastReindexIso hc C V h).symm hc C))

theorem VolumeBlowupEquivalent.product_right
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k n : ℕ} {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V)
    (R : PositiveRVVolumeObject (M := M) (C.base : Set M) n) :
    VolumeBlowupEquivalent (U.prod R) (V.prod R) := by
  have hC := rv_inv_mem_base C.base (rvPermutationSign_mem C.base (positiveProductSwapPermutation k n))
  have h0 := inv_ne_zero (rvPermutationSign_ne_zero (M := M) (positiveProductSwapPermutation k n))
  have hprod := (h.product_left hc C R).reindexDegree hc C (positiveProduct_degree_swap k n)
  have hscaled := hprod.rescale hc C (positiveProductSwapSign (M := M) k n)⁻¹ hC h0
  exact ((VolumeBlowupEquivalent.of_iso C (volumeSignedProductSwapIso hc C U R)).trans hc C
    hscaled).trans hc C
      (VolumeBlowupEquivalent.of_iso C ((volumeSignedProductSwapIso hc C V R).symm hc C))

theorem VolumeBlowupEquivalent.prod
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {k n : ℕ} {U U' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    {V V' : PositiveRVVolumeObject (M := M) (C.base : Set M) n}
    (h : VolumeBlowupEquivalent U U') (g : VolumeBlowupEquivalent V V') :
    VolumeBlowupEquivalent (U.prod V) (U'.prod V') :=
  (h.product_right hc C V).trans hc C (g.product_left hc C U')

end IntegrationInACVF.Section7
