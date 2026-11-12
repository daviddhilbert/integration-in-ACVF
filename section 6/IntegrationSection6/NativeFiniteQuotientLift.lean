import IntegrationSection6.FiniteGammaQuotientLift
import IntegrationSection6.NativeFiniteLiftInvariance
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! Native additive lifting from the finite Gamma common-blowup quotient
to the inherited finite VF scissor presentation. This constructs the
map without a canonical-presentation assumption. -/
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

variable {κ : Cardinal}
variable (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
variable (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)

def nativeGammaPositiveFiniteLift :
    KPlus (gammaRVFinitePresentation B k) →+ KPlus (gammaVFFinitePresentation B k) :=
  lift (gammaRVFinitePresentation B k) {
    toFun := fun U => of (gammaVFFinitePresentation B k) ⟨gammaLiftVF U.val, gammaLiftVF_finite U.val U.property⟩
    iso := fun ⟨e⟩ => of_iso (gammaVFFinitePresentation B k) (gammaRVIso_liftIso hκ hs h00 hsmall hB e)
    empty := of_empty (gammaVFFinitePresentation B k)
    scissor := fun h => of_scissor (gammaVFFinitePresentation B k) (GammaRVScissor.lift h)
  }

theorem nativeGammaPositiveFiniteLift_class (U : GammaRVFiniteObject B k) :
    nativeGammaPositiveFiniteLift hκ hs h00 hsmall hB (gammaFiniteScissorClass U) =
      gammaFiniteLiftScissorClass U :=
  lift_of (gammaRVFinitePresentation B k) _ (gammaFiniteScissorObject U)

include hB in
theorem GammaIspAt.native_lift_class_eq {U V : GammaObjectAt B S k}
    (H : GammaIspAt hκ hs h00 hsmall U V) :
    gammaFiniteLiftScissorClass U.toGamma = gammaFiniteLiftScissorClass V.toGamma :=
  of_iso (gammaVFFinitePresentation B k) (H.liftIsoNative hB)

variable [Fact (B.real ⊆ S)]

def nativeGammaLiftAt : GammaIsoClassesAt B S k →+ KPlus (gammaVFFinitePresentation B k) :=
  (nativeGammaPositiveFiniteLift hκ hs h00 hsmall hB).comp gammaIsoClassesToScissors

@[simp] theorem nativeGammaLiftAt_class (U : GammaObjectAt B S k) :
    nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt U) = gammaFiniteLiftScissorClass U.toGamma := by
  change nativeGammaPositiveFiniteLift hκ hs h00 hsmall hB
    (gammaIsoClassesToScissors (gammaIsoClassAt U)) = _
  rw [gammaIsoClassesToScissors_class,nativeGammaPositiveFiniteLift_class]

theorem nativeGammaIspAt_le_lift_kernel : gammaIspAddConAt (S := S) (n := k) hκ hs h00 hsmall ≤
    AddCon.ker (nativeGammaLiftAt (S := S) (k := k) hκ hs h00 hsmall hB) := by
  rintro a b ⟨U,V,rfl,rfl,H⟩
  change nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt U) =
    nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt V)
  rw [nativeGammaLiftAt_class,nativeGammaLiftAt_class]
  exact H.native_lift_class_eq hκ hs h00 hsmall hB

def nativeGammaQuotientLiftAt : (gammaIspAddConAt (S := S) (n := k) hκ hs h00 hsmall).Quotient →+
    KPlus (gammaVFFinitePresentation B k) :=
  (gammaIspAddConAt hκ hs h00 hsmall).lift (nativeGammaLiftAt hκ hs h00 hsmall hB)
    (nativeGammaIspAt_le_lift_kernel hκ hs h00 hsmall hB)

theorem nativeGammaQuotientLiftAt_class (U : GammaObjectAt B S k) :
    nativeGammaQuotientLiftAt hκ hs h00 hsmall hB
      ((gammaIspAddConAt hκ hs h00 hsmall).mk' (gammaIsoClassAt U)) =
        gammaFiniteLiftScissorClass U.toGamma := by
  change nativeGammaLiftAt hκ hs h00 hsmall hB (gammaIsoClassAt U) = _
  exact nativeGammaLiftAt_class hκ hs h00 hsmall hB U

end IntegrationInACVF.Section6.FiniteRV
