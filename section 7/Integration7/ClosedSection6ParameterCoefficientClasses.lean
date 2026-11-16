module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ParameterCoefficientSemirings
public import Integration7.ClosedSection6GlobalLiftClassEquality
public import IntegrationSection6.ParameterCoefficientClasses
public import IntegrationSection6.ParameterCoefficientSemirings
public import IntegrationSection6.GlobalLiftClassEquality

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
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
variable (FBase : VFFieldBase B.real) (hB : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))


def parameterRVClass {k : ℕ} (x : Fin p → VF (M := M))
    (U : GammaRVFiniteObject (vfParameterCoefficientBase B x) k) :
    ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x :=
  rvGlobalIntegralClass hκ hs h00
    (vfParameterCoefficientBase_real_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    (vfParameterCoefficientBase_field x)
    (vfParameterCoefficientBase_gamma_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    δ (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 hc (vfParameterCoefficientBase_generated hB x) U

theorem parameterRVClass_eq_iff_liftIso {i j : ℕ} (x : Fin p → VF (M := M))
    (U : GammaObjectAt (vfParameterCoefficientBase B x) Set.univ i)
    (V : GammaObjectAt (vfParameterCoefficientBase B x) Set.univ j) :
    parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x U.toGamma =
      parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x V.toGamma ↔
        Nonempty (GammaIso (vfParameterCoefficientBase B x) U.toGamma.lift V.toGamma.lift) :=
  rvGlobalIntegralClass_eq_iff_liftIso hκ hs h00
    (vfParameterCoefficientBase_real_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    (vfParameterCoefficientBase_field x)
    (vfParameterCoefficientBase_gamma_small (aleph0_lt_of_small_vf_field_base h00 FBase hr) hr hg x)
    δ (vfParameterCoefficientBase_gamma_contains x hδ) hδ1 hc (vfParameterCoefficientBase_generated hB x) U V

end IntegrationInACVF.Section7.CompletedSection6
