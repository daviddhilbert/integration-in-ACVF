import Integration7.GammaNamedLemma77
import Integration7.GammaNamedTheorem713

/-! Gamma-named Section 7 class results over `⟨C.base, Ξ⟩`, without any
hypothesis putting the common names of `⟨C.base, Ξ⟩` into `C.base`.

Objects are coded over the named code context (the substructure generated
by `C.base` and the proof-only common names) and are Gamma-definable over
`⟨C.base, Ξ⟩`; morphisms, blowups and contraction programs have Gamma graphs.

* Corollary 7.6, Lemma 7.7: `GammaNamed.gamma_named_corollary_7_6`,
  `GammaNamed.gamma_named_lemma_7_7`.
* Propositions 7.8, 7.9: `HK.gamma_named_proposition_7_8`,
  `HK.gamma_named_lift_on_classes_bijective`, `HK.gammaNamedIntegrationAddEquiv`.
* Theorem 7.10: `HK.gamma_named_theorem_7_10`, `HK.gammaNamedGradedIntegrationEquiv`,
  `HK.gammaNamedIntegrationRingEquiv`.
* Theorem 7.13: `HK.gamma_named_raw_volume_kernel_principal`, `HK.gamma_named_theorem_7_13`.

The standing hypotheses `VFGammaGeneratedBase ⟨C.base, Ξ⟩`, `γ ∈ Ξ`, `1 < γ`,
`#Ξ < C.κ` and the canonical structure are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
variable (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
variable (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)

include hGenerated hγ hγ1 in
/-- **Gamma-named Proposition 7.8 (all degrees).** Two Gamma RV objects have equal
Gamma-named classes exactly when their actual lifts have equal Gamma-named VF classes. -/
theorem gamma_named_proposition_7_8 {n : ℕ}
    (U V : GammaRVObjects (gammaNamedBase C Ξ) ((gammaNamedCodeContext C Ξ hΞ).base : Set M) n) :
    gammaNamedRVClass hc C Ξ hΞ U = gammaNamedRVClass hc C Ξ hΞ V ↔
      gammaNamedVFLiftClass hc C Ξ hΞ U = gammaNamedVFLiftClass hc C Ξ hΞ V := by
  rw [← gamma_named_lift_on_class hc C Ξ hΞ hGenerated U, ← gamma_named_lift_on_class hc C Ξ hΞ hGenerated V]
  exact (gamma_named_lift_on_classes_bijective hc C Ξ hΞ hGenerated γ hγ hγ1 n).injective.eq_iff.symm

end IntegrationInACVF.Section7.HK
