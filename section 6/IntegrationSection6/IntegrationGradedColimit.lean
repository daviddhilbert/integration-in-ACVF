import IntegrationSection6.IntegrationContexts
import IntegrationSection6.IntegrationLocalizationEmbedding
import IntegrationSection6.CompletionGradedColimit

/-! The actual VF Grothendieck group satisfies the graded-colimit
universal property in6.22, with the native nonzero RV components and the
transition multiplication by j = [1]_1 - [RV^{>1}]_1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Algebra Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {κ : Cardinal} {hs : Saturated M κ}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

abbrev IntegrationContext.groupQuotientEquiv (P : IntegrationContext B κ hs) :=
  integrationRingQuotientEquiv P.countable_le hs P.characteristic P.real_small P.field_base P.gamma_small
    P.value P.value_mem P.value_large P.section5_two_order P.generated

def IntegrationContext.gradedColimitComponent (P : IntegrationContext B κ hs) (k : ℕ) :
    letI := P.vfSemiring
    GammaNonzeroClassesAt (B := B) (S := Set.univ) k →+ GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) := by
  letI := P.vfSemiring
  exact P.groupQuotientEquiv.symm.toAddMonoidHom.comp
    (CompletionLocalization.gradedColimitComponent gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt k)

theorem IntegrationContext.gradedColimit_compatible (P : IntegrationContext B κ hs) :
    letI := P.vfSemiring
    CompletionLocalization.Compatible gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt P.gradedColimitComponent := by
  letI := P.vfSemiring
  intro k x
  change P.groupQuotientEquiv.symm (_ : _ ) - P.groupQuotientEquiv.symm _ = P.groupQuotientEquiv.symm _
  exact (map_sub P.groupQuotientEquiv.symm.toAddMonoidHom _ _).symm.trans
    (congrArg P.groupQuotientEquiv.symm
      (CompletionLocalization.gradedColimitComponent_compatible gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt k x))

theorem theorem_6_22_graded_colimit (P : IntegrationContext B κ hs) {X : Type*} [AddCommGroup X]
    (f : ∀ k, GammaNonzeroClassesAt (B := B) (S := Set.univ) k →+ X)
    (hf : CompletionLocalization.Compatible gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt f) :
    letI := P.vfSemiring
    ∃! g : GrothendieckAddGroup (GammaVFAllAdditiveKPlus B) →+ X,
      ∀ k x, g (P.gradedColimitComponent k x) = f k x := by
  letI := P.vfSemiring
  obtain ⟨g,hg,hu⟩ := CompletionLocalization.gradedColimit_universal
    gammaNonzeroOneClassAt gammaNonzeroPositiveClassAt f hf
  refine ⟨g.comp P.groupQuotientEquiv.toAddMonoidHom,?_,?_⟩
  · intro k x
    change g (P.groupQuotientEquiv (P.groupQuotientEquiv.symm _)) = _
    rw [RingEquiv.apply_symm_apply]
    exact hg k x
  · intro h hh
    have he : h.comp P.groupQuotientEquiv.symm.toAddMonoidHom = g := by
      apply hu
      intro k x
      exact hh k x
    apply AddMonoidHom.ext
    intro z
    have hz := DFunLike.congr_fun he (P.groupQuotientEquiv z)
    change h (P.groupQuotientEquiv.symm (P.groupQuotientEquiv z)) = g (P.groupQuotientEquiv z) at hz
    rw [RingEquiv.symm_apply_apply] at hz
    exact hz

end IntegrationInACVF.Section6.FiniteRV
