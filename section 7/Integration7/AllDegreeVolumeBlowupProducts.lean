import Integration7.AllDegreeVolumeProductIsomorphisms
import Integration7.VolumeBlowupRightProducts
import Integration7.ZeroFactorBlowupProducts

/-! Multiplicative congruence of the actual all-degree MuIsp relation.
This includes ordinary RV[0]; the graded semiring assembly is separate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem muIsp_product
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n m : ℕ} {U U' : RVVolumeObject (M := M) (C.base : Set M) n}
    {V V' : RVVolumeObject (M := M) (C.base : Set M) m}
    (h : MuIsp (C.base : Set M) n U U') (g : MuIsp (C.base : Set M) m V V') :
    MuIsp (C.base : Set M) (n+m)
      (rvVolumeProduct (C.base : Set M) n m U V) (rvVolumeProduct (C.base : Set M) n m U' V') := by
  cases n with
  | zero =>
    cases m with
    | zero =>
      obtain ⟨f⟩ := h
      obtain ⟨e⟩ := g
      exact ⟨rvVolumeProductIso hc C (n := 0) (m := 0) (U := U) (U' := U') (V := V) (V' := V') f e⟩
    | succ m =>
      obtain ⟨f⟩ := h
      exact ((VolumeBlowupEquivalent.of_iso C (volumeProductZeroPositiveIso hc C U V)).trans hc C
        ((VolumeBlowupEquivalent.zero_prod hc C f g).reindexDegree hc C (Nat.zero_add m))).trans hc C
          (VolumeBlowupEquivalent.of_iso C ((volumeProductZeroPositiveIso hc C U' V').symm hc C))
  | succ n =>
    cases m with
    | zero =>
      obtain ⟨e⟩ := g
      exact ((VolumeBlowupEquivalent.of_iso C (volumeProductPositiveZeroIso hc C U V)).trans hc C
        (h.prod_zero hc C e)).trans hc C
          (VolumeBlowupEquivalent.of_iso C ((volumeProductPositiveZeroIso hc C U' V').symm hc C))
    | succ m => exact h.prod hc C g

end IntegrationInACVF.Section7
