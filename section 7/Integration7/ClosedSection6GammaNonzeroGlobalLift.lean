module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6GammaGlobalLiftClasses
public import IntegrationSection6.GammaNonzeroGlobalLift
public import IntegrationSection6.GammaGlobalLiftClasses
public import IntegrationSection6.GammaNonzeroGradedSemiring

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
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
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

end IntegrationInACVF.Section7.CompletedSection6
