import IntegrationSection6.Section5TwoOrderInput
import IntegrationSection6.GammaContractionExtensionIsomorphisms

/-! The two-VF-coordinate case of Lemma6.16, using exactly the authorized
Section5.8 refinement and the proved Corollary6.15 for arbitrary contractions.
Internal real presentations may be different and are enlarged internally. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {a : ℕ}

theorem lemma_6_16_two {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
    (h58 : Section5TwoOrderInput B hκ.le hs hreal) (hBS : B.real ⊆ S)
    (U : DefSet (M := M) S 2 a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ υ : Equiv.Perm (Fin 2)} (hσυ : σ 0 ≠ υ 0)
    (T : StandardContraction U σ) (E : StandardContraction U υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    GammaIsp hκ.le hs h00 hreal (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU T hT)
      (gammaFiniteContraction hκ.le hs hreal hBS hU hfinU E hE) := by
  let U' := extendBase U (Set.subset_univ S)
  let T' := extendStandardContraction T (Set.subset_univ S)
  let E' := extendStandardContraction E (Set.subset_univ S)
  let hT' := gamma_extendStandardContraction T (Set.subset_univ S) hT
  let hE' := gamma_extendStandardContraction E (Set.subset_univ S) hE
  obtain ⟨b,V,hV,hfinV,f,hf,hF,hVF,C,D,hC,hD,⟨e⟩⟩ := h58 U' hU hfinU σ υ hσυ
  have hL := corollary_6_15_finite hκ hs h00 hreal hgamma δ hδ hδ1 (Set.subset_univ _)
    U' V hU hV hfinU hfinV f hf hF
    (fun u j _ => congrFun (hVF u) j) T' C hT' hC
  have hR := corollary_6_15_finite hκ hs h00 hreal hgamma δ hδ hδ1 (Set.subset_univ _)
    U' V hU hV hfinU hfinV f hf hF
    (fun u j _ => congrFun (hVF u) j) E' D hE' hD
  have h := hL.trans ((GammaIsp.of_iso e).trans hR.symm)
  exact h.corollary_6_6
    (gammaContractionExtensionIso hκ.le hs hreal hBS (Set.subset_univ S) hU hfinU T hT)
    (gammaContractionExtensionIso hκ.le hs hreal hBS (Set.subset_univ S) hU hfinU E hE)

end IntegrationInACVF.Section6.FiniteRV
