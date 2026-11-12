import IntegrationSection6.GammaGlobalLiftClasses
import IntegrationSection6.GammaNonzeroGradedSemiring

/-! Canonical semiring lifting from actual nonzero graded RV classes
to the actual finite VF semiring. -/
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

theorem gammaAllLiftClass_unit (hBS : B.real ⊆ S) : gammaAllLiftClass (gammaUnitAt hBS).toGamma = 1 := by
  have hU : (gammaUnitAt hBS).toGamma.lift = (Set.univ : Set (Point (M := M) 0 0)) := by
    ext p
    constructor
    · intro _
      exact Set.mem_univ _
    · intro _
      exact ⟨⟨Fin.elim0,Set.mem_univ _⟩,(by funext i; exact i.elim0),(by funext i; exact i.elim0)⟩
  let e := (gammaIso_reflexive (gammaVFAllUnit B).domain (gammaVFAllUnit B).definable).congr hU.symm rfl
  exact (PositiveGrothendieck.of_iso (gammaVFAllPositivePresentation B)
    (b := gammaVFAllUnit B) ⟨e⟩).trans (PositiveGrothendieck.of_unit (gammaVFAllPositivePresentation B))

variable [hBS : Fact (B.real ⊆ S)]

def gammaNonzeroLiftComponentAt (k : ℕ) : GammaNonzeroClassesAt (B := B) (S := S) k →+ GammaVFAllKPlus B :=
  (gammaAllLiftClassesAt hκ hs h00 hsmall hB).comp (gammaNonzeroClassSubmonoidAt k).subtype

def gammaNonzeroGlobalLiftAt : GammaNonzeroGradedAt (B := B) (S := S) →+* GammaVFAllKPlus B :=
  DirectSum.toSemiring (gammaNonzeroLiftComponentAt hκ hs h00 hsmall hB)
    (by
      change gammaAllLiftClassesAt hκ hs h00 hsmall hB (gammaIsoClassAt (gammaUnitAt hBS.out)) = 1
      rw [gammaAllLiftClassesAt_class]
      exact gammaAllLiftClass_unit hBS.out)
    (by
      intro i j a b
      exact gammaAllLiftClassesAt_mul hκ hs h00 hsmall hB a.val b.val)

theorem gammaNonzeroGlobalLiftAt_class (U : GammaObjectAt B S k) (hU : GammaFullWeightAt U) :
    gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB (gammaNonzeroGradedClassAt U hU) = gammaAllLiftClass U.toGamma := by
  change gammaNonzeroGlobalLiftAt hκ hs h00 hsmall hB
    (DirectSum.of (GammaNonzeroClassesAt (B := B) (S := S)) k (gammaNonzeroClassAt U hU)) = _
  rw [gammaNonzeroGlobalLiftAt,DirectSum.toSemiring_of]
  exact gammaAllLiftClassesAt_class hκ hs h00 hsmall hB U

end IntegrationInACVF.Section6.FiniteRV
