import IntegrationSection6.FiniteGammaProductCoherence
import IntegrationSection6.FiniteGammaProductUnit
import IntegrationSection6.FiniteGammaProductIsos
import IntegrationSection6.FiniteGammaProductDistribution
import IntegrationSection6.FiniteGammaProductRightDistribution
import IntegrationSection6.FiniteGammaScissorComparison
import IntegrationSection6.FiniteGammaEmptyIsomorphisms

/-! Graded multiplication on actual Gamma RV[k] isomorphism classes.
The construction follows the pinned Section4.RVHomogeneousProducts pattern;
every comparison here uses a full original-Gamma finite isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k l : ℕ}

def gammaClassMulAt (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) : GammaIsoClassesAt B S (k+l) :=
  gammaIsoClassAt (gammaProductAt (gammaIsoClassRepresentativeAt a) (gammaIsoClassRepresentativeAt b))

@[simp] theorem gammaClassMulAt_class (U : GammaObjectAt B S k) (V : GammaObjectAt B S l) :
    gammaClassMulAt (gammaIsoClassAt U) (gammaIsoClassAt V) = gammaIsoClassAt (gammaProductAt U V) := by
  obtain ⟨e⟩ := gammaIsoClassAt_eq_iff.mp (gammaIsoClassRepresentativeAt_class (gammaIsoClassAt U))
  obtain ⟨f⟩ := gammaIsoClassAt_eq_iff.mp (gammaIsoClassRepresentativeAt_class (gammaIsoClassAt V))
  exact gammaIsoClassAt_iso (gammaProductIsoAt e f)

def gammaClassCastAt (h : k = l) (a : GammaIsoClassesAt B S k) : GammaIsoClassesAt B S l := h ▸ a

theorem gammaClassCastAt_add [Fact (B.real ⊆ S)] (h : k = l) (a b : GammaIsoClassesAt B S k) :
    gammaClassCastAt h (a+b) = gammaClassCastAt h a + gammaClassCastAt h b := by cases h; rfl

theorem gammaClassCastAt_reindex (h : k = l) (U : GammaObjectAt B S k) (e : Fin l ≃ Fin k) :
    gammaClassCastAt h (gammaIsoClassAt U) = gammaIsoClassAt (U.reindexVolume e) := by
  subst l
  exact gammaIsoClassAt_iso (gammaReindexVolumeIsoAt U e)

theorem gammaClassMulAt_comm_cast (a : GammaIsoClassesAt B S k) (b : GammaIsoClassesAt B S l) :
    gammaClassCastAt (Nat.add_comm l k) (gammaClassMulAt b a) = gammaClassMulAt a b := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaClassMulAt_class,gammaClassMulAt_class]
  exact (gammaClassCastAt_reindex (Nat.add_comm l k) (gammaProductAt V U) finAddFlip).trans
    (gammaIsoClassAt_iso (gammaProductCommReindexedIsoAt U V)).symm

theorem gammaClass_heq_of_reindexedIso (h : k = l) (U : GammaObjectAt B S k) (V : GammaObjectAt B S l)
    (e : Fin k ≃ Fin l) (hi : GammaIsoAt U (V.reindexVolume e)) : HEq (gammaIsoClassAt U) (gammaIsoClassAt V) := by
  have hc : gammaClassCastAt h.symm (gammaIsoClassAt V) = gammaIsoClassAt U :=
    (gammaClassCastAt_reindex h.symm V e).trans (gammaIsoClassAt_iso hi).symm
  have hh : HEq (gammaClassCastAt h.symm (gammaIsoClassAt V)) (gammaIsoClassAt V) := by cases h; rfl
  exact (heq_of_eq hc.symm).trans hh

variable [hBS : Fact (B.real ⊆ S)]

theorem gammaClassMulAt_add (a : GammaIsoClassesAt B S k) (b c : GammaIsoClassesAt B S l) :
    gammaClassMulAt a (b+c) = gammaClassMulAt a b + gammaClassMulAt a c := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  obtain ⟨W,rfl⟩ := gammaIsoClassAt_surjective c
  rw [← gammaIsoClassAt_coprod V W,gammaClassMulAt_class,gammaClassMulAt_class,
    gammaClassMulAt_class,← gammaIsoClassAt_coprod]
  exact gammaIsoClassAt_iso (gammaProductRightDistribIsoAt V W U)

theorem gammaClassMulAt_add_left (a b : GammaIsoClassesAt B S k) (c : GammaIsoClassesAt B S l) :
    gammaClassMulAt (a+b) c = gammaClassMulAt a c + gammaClassMulAt b c := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  obtain ⟨W,rfl⟩ := gammaIsoClassAt_surjective c
  rw [← gammaIsoClassAt_coprod U V,gammaClassMulAt_class,gammaClassMulAt_class,
    gammaClassMulAt_class,← gammaIsoClassAt_coprod]
  exact gammaIsoClassAt_iso (gammaProductLeftDistribIsoAt U V W)

end IntegrationInACVF.Section6.FiniteRV
