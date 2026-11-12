import IntegrationSection6.GammaLiftPadding
import IntegrationSection6.GammaPaddingClasses
import IntegrationSection6.FiniteIntegrationEquivalence

/-! Padding preserves and reflects the actual common-blowup congruence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open SpecialTransformations.Section4.PositiveAdditiveGrothendieck
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ} {S : Set M}
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hreal : Cardinal.mk B.real < κ) (FBase : VFFieldBase B.real)
variable (hgamma : Cardinal.mk B.gamma < κ) (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

variable (hB : VFGammaGeneratedBase B)

include FBase hgamma δ hδ hδ1 h58 hB in
theorem gammaIsp_padding_iff (U V : GammaObjectAt B S k) :
    GammaIsp hκ hs h00 hreal (gammaPadAt U).toGamma (gammaPadAt V).toGamma ↔
      GammaIsp hκ hs h00 hreal U.toGamma V.toGamma := by
  constructor
  · intro H
    obtain ⟨e⟩ := H.liftIsoNative hB
    let f := ((gammaLiftPaddingIsoAt U).trans (gammaLogicInput B) e).trans (gammaLogicInput B)
      ((gammaLiftPaddingIsoAt V).symm (gammaLogicInput B))
    exact lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 U.toGamma V.toGamma f
  · intro H
    obtain ⟨e⟩ := H.liftIsoNative hB
    let f := (((gammaLiftPaddingIsoAt U).symm (gammaLogicInput B)).trans (gammaLogicInput B) e).trans
      (gammaLogicInput B) (gammaLiftPaddingIsoAt V)
    exact lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 (gammaPadAt U).toGamma (gammaPadAt V).toGamma f

include FBase hgamma δ hδ hδ1 h58 hB in
theorem gammaClassIspAt_padding_iff (a b : GammaIsoClassesAt B Set.univ k) :
    gammaClassIspAt hκ hs h00 hreal (gammaPaddingClassesAt a) (gammaPaddingClassesAt b) ↔
      gammaClassIspAt hκ hs h00 hreal a b := by
  obtain ⟨U,rfl⟩ := gammaIsoClassAt_surjective a
  obtain ⟨V,rfl⟩ := gammaIsoClassAt_surjective b
  rw [gammaPaddingClassesAt_class,gammaPaddingClassesAt_class,gammaClassIspAt_class_iff,gammaClassIspAt_class_iff]
  constructor
  · intro H
    exact ((gammaIsp_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U V).mp H.to_global).at_univ
  · intro H
    exact ((gammaIsp_padding_iff hκ hs h00 hreal FBase hgamma δ hδ hδ1 h58 hB U V).mpr H.to_global).at_univ

end IntegrationInACVF.Section6.FiniteRV
