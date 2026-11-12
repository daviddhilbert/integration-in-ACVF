import IntegrationSection6.KernelPositiveDegree
import IntegrationSection6.KernelDegreeZero

/-! Lemma6.17's kernel implication in every finite RV degree. The full
biconditional here retains the previously explicit canonical-presentation
boundary of general-chart lift invariance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem lemma_6_17_kernel_uncountable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ.le hs)
    (U V : GammaRVFiniteObject B k) (e : GammaIso B U.lift V.lift) : GammaIsp hκ.le hs h00 hreal U V := by
  cases k with
  | zero => exact GammaIsp.of_iso (gamma_zero_lift_iso U V e)
  | succ n => exact lemma_6_17_kernel_positive hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 U V e

theorem lemma_6_17_kernel {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ hs)
    (U V : GammaRVFiniteObject B k) (e : GammaIso B U.lift V.lift) : GammaIsp hκ hs h00 hreal U V :=
  lemma_6_17_kernel_uncountable (aleph0_lt_of_small_vf_field_base h00 FBase hreal)
    hs h00 hreal hgamma δ hδ hδ1 FBase h58 U V e

theorem lemma_6_17_with_canonical_presentation
    (hcan : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (h58 : Section5TwoOrderInputAll hκ hs) (U V : GammaRVFiniteObject B k) :
    Nonempty (GammaIso B U.lift V.lift) ↔ GammaIsp hκ hs h00 hreal U V := by
  constructor
  · rintro ⟨e⟩
    exact lemma_6_17_kernel hκ hs h00 hreal hgamma δ hδ hδ1 FBase h58 U V e
  · intro H
    exact H.liftIso hcan hB

end IntegrationInACVF.Section6.FiniteRV
