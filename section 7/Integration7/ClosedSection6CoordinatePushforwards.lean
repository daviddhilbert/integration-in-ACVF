module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ProjectionRepresentativeIndependence
public import IntegrationSection6.CoordinatePushforwards
public import IntegrationSection6.ProjectionRepresentativeIndependence

@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ} {n p : ℕ}

def coordinatePushforward (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) : P.Function A → P.Function (E.baseImage A) :=
  Quotient.lift (fun F => Quotient.mk _ (projectionRepresentative P E A hA F))
    (fun F G he => projectionRepresentative_independent P E A hA F G he)

theorem coordinatePushforward_value (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A)
    (x : E.baseImage A) :
    P.functionValue (E.baseImage A) (coordinatePushforward P E A hA (Quotient.mk _ F)) x =
      projectionFibreIntegral P E A hA F x :=
  projectionRepresentative_value P E A hA F x

theorem coordinatePushforward_integral (P : IntegrationContext B κ hs) (E : VFCoordinateProjection n p)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (f : P.Function A) :
    P.integral (E.baseImage A) (E.gamma_baseImage A hA) (coordinatePushforward P E A hA f) = P.integral A hA f := by
  induction f using Quotient.inductionOn with
  | h F => exact projectionRepresentative_integral P E A hA F

theorem proposition_6_21 (P : IntegrationContext B κ hs)
    (A : Set (Point (M := M) n 0)) (hA : GammaSetDefinable B A) (f : P.Function A)
    (E₁ E₂ : Set (Fin n)) (_h₁ : E₁.Nonempty) (_h₂ : E₂.Nonempty) :
    P.integral ((VFCoordinateProjection.ofSet E₁).baseImage A)
        ((VFCoordinateProjection.ofSet E₁).gamma_baseImage A hA)
        (coordinatePushforward P (VFCoordinateProjection.ofSet E₁) A hA f) =
      P.integral ((VFCoordinateProjection.ofSet E₂).baseImage A)
        ((VFCoordinateProjection.ofSet E₂).gamma_baseImage A hA)
        (coordinatePushforward P (VFCoordinateProjection.ofSet E₂) A hA f) := by
  exact (coordinatePushforward_integral P _ A hA f).trans (coordinatePushforward_integral P _ A hA f).symm

end IntegrationInACVF.Section7.CompletedSection6
