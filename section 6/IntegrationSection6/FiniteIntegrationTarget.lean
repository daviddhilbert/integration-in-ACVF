import IntegrationSection6.Kernel
import IntegrationSection6.GammaIspUniversalPresentation
import IntegrationSection6.FiniteGammaAdditiveCongruence

/-! The actual fixed-degree target of integration: RV[k] isomorphism
classes modulo the proved common-blowup congruence. The internal real
presentation is common to all objects and is never bounded by saturation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ)

abbrev IntegrationTarget (k : ℕ) :=
  (gammaIspAddConAt (B := B) (S := Set.univ) (n := k) hκ hs h00 hreal).Quotient

def rvIntegralClass (U : GammaRVFiniteObject B k) : IntegrationTarget hκ hs h00 hreal k :=
  (gammaIspAddConAt hκ hs h00 hreal).mk' (gammaIsoClassAt (gammaUniversalObject U))

theorem rvIntegralClass_eq_iff (U V : GammaRVFiniteObject B k) :
    rvIntegralClass hκ hs h00 hreal U = rvIntegralClass hκ hs h00 hreal V ↔ GammaIsp hκ hs h00 hreal U V := by
  constructor
  · intro he
    have H := (gammaIspAddConAt hκ hs h00 hreal).eq.mp he
    have HAt := (gammaClassIspAt_class_iff _ _).mp H
    exact GammaIsp.of_presented (Set.subset_univ _) (Set.subset_univ _) HAt.to_global
  · intro H
    exact (gammaIspAddConAt hκ hs h00 hreal).eq.mpr ((gammaClassIspAt_class_iff _ _).mpr H.at_univ)

theorem rvIntegralClass_iso {U V : GammaRVFiniteObject B k}
    (e : GammaRVIso U.toGammaRVObject V.toGammaRVObject) :
    rvIntegralClass hκ hs h00 hreal U = rvIntegralClass hκ hs h00 hreal V :=
  (rvIntegralClass_eq_iff hκ hs h00 hreal U V).mpr (GammaIsp.of_iso e)

theorem rvIntegralClass_at (U : GammaObjectAt B Set.univ k) :
    rvIntegralClass hκ hs h00 hreal U.toGamma =
      (gammaIspAddConAt hκ hs h00 hreal).mk' (gammaIsoClassAt U) := rfl

theorem rvIntegralClass_empty :
    rvIntegralClass hκ hs h00 hreal (gammaEmptyAt (B := B) (n := k) (S := Set.univ) (Set.subset_univ _)).toGamma = 0 := by
  rw [rvIntegralClass_at,gammaIsoClassAt_empty,map_zero]

theorem rvIntegralClass_coprod (U V : GammaObjectAt B Set.univ k) :
    rvIntegralClass hκ hs h00 hreal (gammaCoprodAt U V).toGamma =
      rvIntegralClass hκ hs h00 hreal U.toGamma + rvIntegralClass hκ hs h00 hreal V.toGamma := by
  rw [rvIntegralClass_at,rvIntegralClass_at,rvIntegralClass_at,gammaIsoClassAt_coprod,map_add]

end IntegrationInACVF.Section6.FiniteRV
