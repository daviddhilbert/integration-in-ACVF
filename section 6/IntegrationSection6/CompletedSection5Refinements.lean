module

public import IntegrationSection5.FiniteRVComparison
public import IntegrationSection6.CompletedSection5Comparisons
public import IntegrationSection6.GammaContractionExtensionIsomorphisms

@[expose] public section

/-! The published finite Section 5.8 producer supplies the actual
VF-fixed refinement and the normalized opposite-order comparison over its
recorded standing parameter hypotheses. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem completed_section5_two_order_refinement {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (B : Base (M := M))
    (hsmall : Cardinal.mk B.real < κ) (hGenerated : VFGammaGeneratedBase B)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ) (FBase : VFFieldBase B.real)
    {a : ℕ} (U : DefSet (M := M) Set.univ 2 a) (hU : GammaSetDefinable B (carrier U))
    (hfinU : ∀ x : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite) :
    ∃ b : ℕ, ∃ V : DefSet (M := M) Set.univ 2 b,
    ∃ hV : GammaSetDefinable B (carrier V),
    ∃ hfinV : ∀ x : Fin 2 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite,
    ∃ f : Map U V, Function.Bijective f ∧ GammaGraphDefinable B (pointMapGraph f) ∧
      (∀ u : U, (f u).val.1 = u.val.1) ∧
    ∃ T : StandardContraction V (Equiv.refl _), ∃ E : StandardContraction V (Equiv.swap 0 1),
    ∃ hT : GammaProgramDefinable B T.program, ∃ hE : GammaProgramDefinable B E.program,
    Nonempty (SpecialTransformations.Section7.GammaRVIso
      (gammaFiniteContraction hκ hs hsmall (Set.subset_univ _) hV hfinV T hT).toGammaRVObject
      (gammaFiniteContraction hκ hs hsmall (Set.subset_univ _) hV hfinV E hE).toGammaRVObject) := by
  obtain ⟨L⟩ := lemma_5_8_finite hκ hs h00 B hsmall hGenerated δ hδ hδ1 FBase (carrier U) hU hfinU
  let Q := L.comparison
  let V := extendBase Q.source (Set.subset_univ Q.codes)
  have hV : GammaSetDefinable B (carrier V) := Q.source_gamma
  have hFinTarget := GammaIso.finite_mixed_rv_fibres hκ hs hsmall L.injection.iso hfinU
  have hfinV : ∀ x : Fin 2 → VF (M := M),
      {r : Fin L.injection.arity → RV (M := M) | (x,r) ∈ carrier V}.Finite :=
    Q.source_eq.symm ▸ hFinTarget
  let e : U ≃ V := L.injection.iso.equiv.trans (Set.equivOfEq Q.source_eq.symm)
  have he (u : U) : (e u).val = (L.injection.iso.equiv u).val := by
    simp only [e,Equiv.trans_apply,Set.equivOfEq_apply]
  have hGraph : GammaGraphDefinable B (fun p q => ∃ u : U, u.val = p ∧ (e u).val = q) := by
    apply GammaGraphDefinable.congr L.injection.iso.graph
    intro p q
    constructor
    · rintro ⟨u,hu,hq⟩
      exact ⟨u,hu,(he u).trans hq⟩
    · rintro ⟨u,hu,hq⟩
      exact ⟨u,hu,(he u).symm.trans hq⟩
  obtain ⟨d,t,hReal⟩ := hGraph.real_specialize
  let f : Map U V := Map.mk e (RelationDefinable.mono _ _ hReal (Set.subset_univ _))
  have hf : Function.Bijective f := e.bijective
  have hVF : ∀ u : U, (f u).val.1 = u.val.1 := by
    intro u
    exact (congrArg Prod.fst (he u)).trans (L.injection.fixes_vf u)
  let T := extendStandardContraction Q.contraction12 (Set.subset_univ Q.codes)
  let E := extendStandardContraction Q.contraction21 (Set.subset_univ Q.codes)
  let hT := gamma_extendStandardContraction Q.contraction12 (Set.subset_univ Q.codes) Q.program12_gamma
  let hE := gamma_extendStandardContraction Q.contraction21 (Set.subset_univ Q.codes) Q.program21_gamma
  have e0 := gammaStandardComparisonOfNativeIso hκ hs hsmall Q.real_contains Q.source_gamma
    (Q.source_eq.symm ▸ hFinTarget) Q.contraction12 Q.contraction21 Q.program12_gamma Q.program21_gamma Q.comparison
  have eT := gammaContractionExtensionIso hκ hs hsmall Q.real_contains (Set.subset_univ Q.codes)
    Q.source_gamma (Q.source_eq.symm ▸ hFinTarget) Q.contraction12 Q.program12_gamma
  have eE := gammaContractionExtensionIso hκ hs hsmall Q.real_contains (Set.subset_univ Q.codes)
    Q.source_gamma (Q.source_eq.symm ▸ hFinTarget) Q.contraction21 Q.program21_gamma
  exact ⟨L.injection.arity,V,hV,hfinV,f,hf,hGraph,hVF,T,E,hT,hE,
    ⟨gammaIsoTrans (gammaIsoSymm eT) (gammaIsoTrans e0 eE)⟩⟩

end IntegrationInACVF.Section6.FiniteRV
