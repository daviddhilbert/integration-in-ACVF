module

public import Integration7.PositiveGradedCoordinatePushforwards
public import Integration7.NonemptyVolumeCoordinateProjections

@[expose] public section

/-! Raw Fubini for finite sums of positive homogeneous function values.
Every nonempty retained coordinate set is included, and coefficients
still range over the complete raw graded semiring, including RV[0]. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open Classical
open scoped DirectSum
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n p q : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (⟨(C.base : Set M),Ξ⟩ : Base (M := M)))
variable (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

theorem positive_graded_signed_coordinate_integral_eq_total
    (E : VFCoordinateProjection (n+1) (p+1)) (f : PositiveGradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
      positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | of j f =>
    rw [positive_graded_signed_coordinate_of,positive_graded_ae_volume_integral_of,
      positive_graded_ae_volume_integral_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext
      (by change appendVolumeDegree (p+1) (appendVolumeDegree E.discarded j)+1 = appendVolumeDegree (n+1) j+1
          have h := volume_projection_index_eq E
          simp only [append_volume_degree_eq] at *
          omega)
      (positive_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f))

theorem positive_graded_volume_fubini
    (E : VFCoordinateProjection (n+1) (p+1)) (D : VFCoordinateProjection (n+1) (q+1))
    (f : PositiveGradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 p
      (positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f) =
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 q
      (positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f) :=
  (positive_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 E f).trans
    (positive_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 D f).symm

theorem positive_graded_nonempty_coordinate_integral
    (E : Set (Fin (n+1))) (hE : E.Nonempty) (f : PositiveGradedAEVolumeFunction hc C n) :
    positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 ((Fintype.card E).pred)
      (positiveGradedAEVolumeSignedCoordinatePushforward hc C Ξ hΞ hGenerated hNames γ hγ hγ1
        (nonemptyVolumeCoordinateProjection E hE) f) =
      positiveGradedAEVolumeIntegral hc C Ξ hΞ hGenerated hNames γ hγ hγ1 n f :=
  positive_graded_signed_coordinate_integral_eq_total hc C Ξ hΞ hGenerated hNames γ hγ hγ1 _ f
end IntegrationInACVF.Section7
