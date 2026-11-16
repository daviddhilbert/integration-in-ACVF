module

public import Integration7.GeneratedKernelPositiveDegree
public import IntegrationSection6.KernelEquivalence
public import IntegrationSection6.VFParameterCoefficientBases

@[expose] public section

/-! The actual Section6 kernel theorem over its standing generated base,
with no universal two-order premise. The final namespace gives the same
fixed-degree integration interface with a canonical-model certificate in
place of that open premise. Generation is a proved standing base property. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k : ℕ}

theorem generated_kernel_uncountable {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (U V : GammaRVFiniteObject B k) (e : GammaIso B U.lift V.lift) : GammaIsp hκ.le hs h00 hreal U V := by
  cases k with
  | zero => exact GammaIsp.of_iso (gamma_zero_lift_iso U V e)
  | succ n => exact generated_kernel_positive hκ hs h00 hc hreal hgamma hB δ hδ hδ1 FBase U V e

theorem generated_kernel {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (U V : GammaRVFiniteObject B k) (e : GammaIso B U.lift V.lift) : GammaIsp hκ hs h00 hreal U V :=
  generated_kernel_uncountable (aleph0_lt_of_small_vf_field_base h00 FBase hreal)
    hs h00 hc hreal hgamma hB δ hδ hδ1 FBase U V e

theorem generated_lemma_6_17 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (U V : GammaRVFiniteObject B k) :
    Nonempty (GammaIso B U.lift V.lift) ↔ GammaIsp hκ hs h00 hreal U V :=
  ⟨fun ⟨e⟩ => generated_kernel hκ hs h00 hc hreal hgamma hB δ hδ hδ1 FBase U V e,
    fun H => H.liftIsoNative hB⟩

instance generatedVFParameterBaseFact [Fact (VFGammaGeneratedBase B)] {p : ℕ} (x : Fin p → VF (M := M)) :
    Fact (VFGammaGeneratedBase (vfParameterCoefficientBase B x)) :=
  ⟨vfParameterCoefficientBase_generated Fact.out x⟩

namespace CompletedSection6

theorem lemma_6_17_kernel {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hc : CanonicalStructure.IsCanonical (M := M)) [hgen : Fact (VFGammaGeneratedBase B)]
    (U V : GammaRVFiniteObject B k) (e : GammaIso B U.lift V.lift) : GammaIsp hκ hs h00 hreal U V :=
  generated_kernel hκ hs h00 hc hreal hgamma Fact.out δ hδ hδ1 FBase U V e

theorem lemma_6_17 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ) (hB : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    (hc : CanonicalStructure.IsCanonical (M := M)) (U V : GammaRVFiniteObject B k) :
    Nonempty (GammaIso B U.lift V.lift) ↔ GammaIsp hκ hs h00 hreal U V :=
  generated_lemma_6_17 hκ hs h00 hc hreal hgamma hB δ hδ hδ1 FBase U V
end CompletedSection6
end IntegrationInACVF.Section7
