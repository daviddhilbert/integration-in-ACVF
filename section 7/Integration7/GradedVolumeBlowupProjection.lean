import Integration7.AllDegreeVolumeBlowupSemiring

/-! The actual graded quotient projection is a surjective semiring
homomorphism, assembled from the fixed-degree additive projections. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def rvVolumeGradedBlowupProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    RVVolumeIsoSemiring hc C →+* RVVolumeBlowupSemiring hc C := by
  let F (n : ℕ) := (DirectSum.of (RVVolumeBlowupClasses hc C) n).comp (rvVolumeBlowupProjection hc C n)
  apply DirectSum.toSemiring F
  · rfl
  · intro n m a b
    change DirectSum.of (RVVolumeBlowupClasses hc C) (n+m)
      (rvVolumeBlowupProjection hc C (n+m) (rvVolumeIsoClassesProduct hc C n m a b)) =
        DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupProjection hc C n a) *
          DirectSum.of (RVVolumeBlowupClasses hc C) m (rvVolumeBlowupProjection hc C m b)
    rw [DirectSum.of_mul_of]
    exact congrArg (DirectSum.of (RVVolumeBlowupClasses hc C) (n+m))
      (rvVolumeBlowupProjection_product hc C n m a b)

@[simp] theorem rvVolumeGradedBlowupProjection_of
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (n : ℕ) (a : RVVolumeIsoClasses hc C n) :
    rvVolumeGradedBlowupProjection hc C (DirectSum.of (RVVolumeIsoClasses hc C) n a) =
      DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupProjection hc C n a) := by
  change DirectSum.toAddMonoid
    (fun i => (DirectSum.of (RVVolumeBlowupClasses hc C) i).comp (rvVolumeBlowupProjection hc C i))
    (DirectSum.of (RVVolumeIsoClasses hc C) n a) = _
  exact DirectSum.toAddMonoid_of _ n a

theorem rvVolumeGradedBlowupProjection_surjective
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) :
    Function.Surjective (rvVolumeGradedBlowupProjection hc C) := by
  intro a
  induction a using DirectSum.induction_on with
  | zero => exact ⟨0,map_zero _⟩
  | of n a =>
    obtain ⟨b,hb⟩ := rvVolumeBlowupProjection_surjective hc C n a
    refine ⟨DirectSum.of (RVVolumeIsoClasses hc C) n b,?_⟩
    rw [rvVolumeGradedBlowupProjection_of,hb]
  | add a b ha hb =>
    obtain ⟨x,hx⟩ := ha
    obtain ⟨y,hy⟩ := hb
    exact ⟨x+y,(map_add _ x y).trans (congrArg₂ (fun x y => x+y) hx hy)⟩

end IntegrationInACVF.Section7
