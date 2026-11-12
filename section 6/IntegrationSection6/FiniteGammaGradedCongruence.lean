import IntegrationSection6.FiniteGammaGradedSemiring
import IntegrationSection6.FiniteGammaProductCongruence
import IntegrationSection6.GradedCongruence

/-! Lemma6.8 on actual original-Gamma finite-volume RV[k] classes,
including the componentwise semiring congruence after grading. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} [Fact (B.real ⊆ S)]
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hsmall : Cardinal.mk B.real < κ)

theorem gammaClassIspAt_mul {k l : ℕ} {a b : GammaIsoClassesAt B S k} {c d : GammaIsoClassesAt B S l}
    (H : gammaClassIspAt hκ hs h00 hsmall a b) (G : gammaClassIspAt hκ hs h00 hsmall c d) :
    gammaClassIspAt hκ hs h00 hsmall (gammaClassMulAt a c) (gammaClassMulAt b d) := by
  obtain ⟨U,V,rfl,rfl,H⟩ := H
  obtain ⟨R,T,rfl,rfl,G⟩ := G
  rw [gammaClassMulAt_class,gammaClassMulAt_class]
  exact (gammaClassIspAt_class_iff _ _).mpr (H.product G)

def gammaIspRingConAt : RingCon (GammaGradedClassesAt B S) :=
  GradedCongruence.congruence (fun _ => gammaIspAddConAt hκ hs h00 hsmall)
    (fun H G => gammaClassIspAt_mul hκ hs h00 hsmall H G)

theorem gammaIspRingConAt_iff (a b : GammaGradedClassesAt B S) :
    gammaIspRingConAt hκ hs h00 hsmall a b ↔
      ∀ k, gammaClassIspAt hκ hs h00 hsmall (a k) (b k) :=
  GradedCongruence.congruence_iff _ _ a b

theorem gammaIspRingConAt_class_iff {k : ℕ} (U V : GammaObjectAt B S k) :
    gammaIspRingConAt hκ hs h00 hsmall (gammaGradedClassAt U) (gammaGradedClassAt V) ↔
      GammaIspAt hκ hs h00 hsmall U V :=
  (GradedCongruence.congruence_of_iff _ _ k (gammaIsoClassAt U) (gammaIsoClassAt V)).trans
    (gammaClassIspAt_class_iff U V)

end IntegrationInACVF.Section6.FiniteRV
