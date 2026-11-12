import IntegrationSection6.FiniteGammaGradedCongruence
import IntegrationSection6.FiniteGammaGenerators
import IntegrationSection6.GradedCongruenceLeast

/-! The genuine finite Gamma common-blowup congruence is the least graded
semiring congruence containing actual elementary blowup replacements. -/
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

theorem gammaIspRingConAt_least (q : RingCon (GammaGradedClassesAt B S))
    (hgen : ∀ (n : ℕ) (U : GammaObjectAt B S n) (i : Fin n)
      (hAd : GammaAdmissible U.toGamma.toGammaRVObject i),
      q (gammaGradedClassAt U) (gammaGradedClassAt (gammaElementaryAt hκ hs h00 hsmall U i hAd))) :
    gammaIspRingConAt hκ hs h00 hsmall ≤ q := by
  apply GradedCongruence.congruence_least _ _ q
  intro n a b hab
  let d : AddCon (GammaIsoClassesAt B S n) := AddCon.comap (DirectSum.of (GammaIsoClassesAt B S) n)
    (fun x y => (DirectSum.of (GammaIsoClassesAt B S) n).map_add x y) q.toAddCon
  have hd : ∀ (U : GammaObjectAt B S n) (i : Fin n)
      (hAd : GammaAdmissible U.toGamma.toGammaRVObject i),
      d (gammaIsoClassAt U) (gammaIsoClassAt (gammaElementaryAt hκ hs h00 hsmall U i hAd)) :=
    hgen n
  exact (gammaIspAddConAt_least d hd) hab

def gammaGradedElementaryRelationAt (a b : GammaGradedClassesAt B S) : Prop :=
  ∃ (n : ℕ) (U : GammaObjectAt B S n) (i : Fin n)
    (hAd : GammaAdmissible U.toGamma.toGammaRVObject i),
    gammaGradedClassAt U = a ∧ gammaGradedClassAt (gammaElementaryAt hκ hs h00 hsmall U i hAd) = b

theorem gammaIspRingConAt_eq_generated : gammaIspRingConAt (S := S) hκ hs h00 hsmall =
    ringConGen (gammaGradedElementaryRelationAt (S := S) hκ hs h00 hsmall) := by
  apply le_antisymm
  · apply gammaIspRingConAt_least hκ hs h00 hsmall
    intro n U i hAd
    exact RingConGen.Rel.of _ _ ⟨n,U,i,hAd,rfl,rfl⟩
  · apply RingCon.ringConGen_le.mpr
    rintro a b ⟨n,U,i,hAd,rfl,rfl⟩
    exact (gammaIspRingConAt_class_iff hκ hs h00 hsmall _ _).mpr
      (gammaElementary_ispAt hκ hs h00 hsmall U i hAd)

end IntegrationInACVF.Section6.FiniteRV
