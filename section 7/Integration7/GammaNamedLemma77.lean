import Integration7.GammaNamedCorollary76
import Integration7.GammaNamedCoproductLifts
import Integration7.GammaNamedCodeContexts

/-! **Gamma-named Corollary 7.6 and Lemma 7.7** over the original base
`⟨C.base, Ξ⟩`. Positive VF volume objects are coded over the named code
context and Gamma-definable over `⟨C.base, Ξ⟩`; contraction programs are
Gamma-definable. The common-name and genericity conditions of the code
context are discharged here, so no hypothesis puts the common names of
`⟨C.base, Ξ⟩` into `C.base`. Lemma 7.7 is stated in the stronger form of
independence of the contraction order. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

/-- **Gamma-named Corollary 7.6** over `⟨C.base, Ξ⟩`. -/
theorem gamma_named_corollary_7_6
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) 𝔖 k)
    (hU : VFVolumeObjectGamma U 𝔅) (hV : VFVolumeObjectGamma V 𝔅)
    (f : VFVolumeBijection U V) (hf : GammaGraphDefinable 𝔅 (vfMixedMapGraph f.map))
    {σ : Equiv.Perm (Fin (k+1))}
    (hi : ∀ p : U.domain, ∀ j, j ≠ σ 0 → (f.map p).val.1 j = p.val.1 j)
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) σ)
    (hT : GammaProgramDefinable 𝔅 T.program) (hE : GammaProgramDefinable 𝔅 E.program) :
    CommonContextVolumeEquivalent 𝔅 𝔇
      ⟨U.standardContractionObject hc 𝔇 Ξ T,
        standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) U hU T hT⟩
      ⟨V.standardContractionObject hc 𝔇 Ξ E,
        standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) V hV E hE⟩ :=
  corollary_7_6 hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) hΞ
    (fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx) γ hγ hγ1 U V hU hV f hf hi T E hT hE

/-- **Gamma-named Lemma 7.7** over `⟨C.base, Ξ⟩`, in the form of order independence:
any two standard contractions of a Gamma-named positive VF volume object, in arbitrary
coordinate orders, give common-context blowup-equivalent RV objects. -/
theorem gamma_named_lemma_7_7
    (hGenerated : VFGammaGeneratedBase (gammaNamedBase C Ξ))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U : PositiveVFVolumeObject (M := M) 𝔖 k) (hU : VFVolumeObjectGamma U 𝔅)
    {σ υ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) υ)
    (hT : GammaProgramDefinable 𝔅 T.program) (hE : GammaProgramDefinable 𝔅 E.program) :
    CommonContextVolumeEquivalent 𝔅 𝔇
      ⟨U.standardContractionObject hc 𝔇 Ξ T,
        standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) U hU T hT⟩
      ⟨U.standardContractionObject hc 𝔇 Ξ E,
        standard_contraction_object_gamma hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) U hU E hE⟩ :=
  relative_volume_contractions_all_orders hc 𝔇 𝔅 (gamma_named_code_context_base C Ξ hΞ) hΞ hGenerated
    (gamma_named_code_context_names C Ξ hΞ) (fun x hx => gamma_named_code_context_generic C Ξ hΞ hc x hx)
    γ hγ hγ1 U U hU hU (VFVolumeBijection.refl hc 𝔇 U)
    (vf_identity_map_gamma _ (fun _ => rfl) hU.domain) 0 (fun _ _ _ => rfl) T E hT hE

end IntegrationInACVF.Section7.GammaNamed
