import IntegrationSection6.FiniteGammaScissorComparison
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! Actual additive lifting from the finite Gamma common-blowup quotient
to the inherited finite VF scissor presentation. This constructs the
forward map; injectivity still requires the geometric kernel theorem6.17. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k : ℕ}

def gammaFiniteLiftScissorClass (U : GammaRVFiniteObject B k) : KPlus (gammaVFFinitePresentation B k) :=
  of (gammaVFFinitePresentation B k) ⟨gammaLiftVF U.toGammaRVObject,
    gammaLiftVF_finite U.toGammaRVObject U.finite_volume⟩

variable (hcan : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

theorem gammaPositiveFiniteLift_class (U : GammaRVFiniteObject B k) :
    gammaPositiveFiniteLift hcan hκ hs h00 hsmall hB (gammaFiniteScissorClass U) =
      gammaFiniteLiftScissorClass U :=
  lift_of (gammaRVFinitePresentation B k) _ (gammaFiniteScissorObject U)

include hcan hB in
theorem GammaIspAt.lift_class_eq {U V : GammaObjectAt B S k}
    (H : GammaIspAt hκ hs h00 hsmall U V) :
    gammaFiniteLiftScissorClass U.toGamma = gammaFiniteLiftScissorClass V.toGamma :=
  of_iso (gammaVFFinitePresentation B k) (H.liftIso hcan hB)

variable [Fact (B.real ⊆ S)]

def gammaLiftAt : GammaIsoClassesAt B S k →+ KPlus (gammaVFFinitePresentation B k) :=
  (gammaPositiveFiniteLift hcan hκ hs h00 hsmall hB).comp gammaIsoClassesToScissors

@[simp] theorem gammaLiftAt_class (U : GammaObjectAt B S k) :
    gammaLiftAt hcan hκ hs h00 hsmall hB (gammaIsoClassAt U) = gammaFiniteLiftScissorClass U.toGamma := by
  change gammaPositiveFiniteLift hcan hκ hs h00 hsmall hB
    (gammaIsoClassesToScissors (gammaIsoClassAt U)) = _
  rw [gammaIsoClassesToScissors_class,gammaPositiveFiniteLift_class]

theorem gammaIspAt_le_lift_kernel : gammaIspAddConAt (S := S) (n := k) hκ hs h00 hsmall ≤
    AddCon.ker (gammaLiftAt (S := S) (k := k) hcan hκ hs h00 hsmall hB) := by
  rintro a b ⟨U,V,rfl,rfl,H⟩
  change gammaLiftAt hcan hκ hs h00 hsmall hB (gammaIsoClassAt U) =
    gammaLiftAt hcan hκ hs h00 hsmall hB (gammaIsoClassAt V)
  rw [gammaLiftAt_class,gammaLiftAt_class]
  exact H.lift_class_eq hcan hκ hs h00 hsmall hB

def gammaQuotientLiftAt : (gammaIspAddConAt (S := S) (n := k) hκ hs h00 hsmall).Quotient →+
    KPlus (gammaVFFinitePresentation B k) :=
  (gammaIspAddConAt hκ hs h00 hsmall).lift (gammaLiftAt hcan hκ hs h00 hsmall hB)
    (gammaIspAt_le_lift_kernel hcan hκ hs h00 hsmall hB)

theorem gammaQuotientLiftAt_class (U : GammaObjectAt B S k) :
    gammaQuotientLiftAt hcan hκ hs h00 hsmall hB
      ((gammaIspAddConAt hκ hs h00 hsmall).mk' (gammaIsoClassAt U)) =
        gammaFiniteLiftScissorClass U.toGamma := by
  change gammaLiftAt hcan hκ hs h00 hsmall hB (gammaIsoClassAt U) = _
  exact gammaLiftAt_class hcan hκ hs h00 hsmall hB U

end IntegrationInACVF.Section6.FiniteRV
