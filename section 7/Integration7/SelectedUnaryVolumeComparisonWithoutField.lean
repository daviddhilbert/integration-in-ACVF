import Integration7.UnaryFibrewiseVolumeComparisonWithoutField
import Integration7.SelectedFamilyVolumePreparation

/-! The one-VF-coordinate instance of positive selected Lemma 7.5
for actual volume families and arbitrary standard contractions of their
density graphs. No coefficient-field condition or prepared-family agreement is
assumed by the caller. Internal coefficient names are eliminated. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {a b k : ℕ}

set_option maxHeartbeats 3200000 in
theorem selected_unary_volume_comparison_without_field
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : SelectedVFVolumeFamily C 1 a k) (G : SelectedVFVolumeFamily C 1 b k)
    (hCommon : ∀ x, VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x))
    {σ υ : Equiv.Perm (Fin 1)}
    (T : StandardContraction (nativeMixedVolumeDomain hc F.densityGraph.domain) σ)
    (E : StandardContraction (nativeMixedVolumeDomain hc G.densityGraph.domain) υ)
    (hT : GammaProgramDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) T.program)
    (hE : GammaProgramDefinable (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) E.program) :
    let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let U := nativeMixedVolumeDomain hc F.densityGraph.domain
    let V := nativeMixedVolumeDomain hc G.densityGraph.domain
    let hU : GammaSetDefinable B (carrier U) := (gammaLogicInput B).real_set _ (setDefinable U)
    let hV : GammaSetDefinable B (carrier V) := (gammaLogicInput B).real_set _ (setDefinable V)
    let RU := FiniteRV.gammaPrependSelectedContraction C.uncountable.le C.saturated C.small
      (Set.Subset.refl _) hU F.densityGraph.selected F.densityGraph.finite_selected T hT
    let RV := FiniteRV.gammaPrependSelectedContraction C.uncountable.le C.saturated C.small
      (Set.Subset.refl _) hV G.densityGraph.selected G.densityGraph.finite_selected E hE
    ∃ hRU : ∀ u : rvObjectDomain RU.object,
        (u.val (FiniteRV.contractionOldLabelIndex T (Fin.last a))).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object,
        (u.val (FiniteRV.contractionOldLabelIndex E (Fin.last b))).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RU hRD (FiniteRV.contractionOldLabelIndex T (Fin.last a)) hRU)
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RV hVD (FiniteRV.contractionOldLabelIndex E (Fin.last b)) hRV) := by
  intro B U V hU hV RU RV
  let A := PresentedSet.univ (pointSpace (M := M) 1 0) (C.base : Set M)
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  obtain ⟨NF,hNF⟩ := F.densityGraphSchema_uniform_bound hc Ξ hΞ
  obtain ⟨NG,hNG⟩ := G.densityGraphSchema_uniform_bound hc Ξ hΞ
  let LF := (F.densityGraphSchema hc Ξ).withBound NF
  let RF := (G.densityGraphSchema hc Ξ).withBound NG
  have hDF : ∀ x : A, ∀ r w, LF.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ LF.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r (Fin.last a) := by
    intro x r w
    exact (gammaSelectedVolumeSchema_density U hU F.densityGraph.selected (Fin.last a)
      (fun q hq => F.densityGraph_label_nonzero q hq) x.val.1 r w).trans
      (and_congr (Set.ext_iff.mp (gammaSelectedLabelSchema_domain U hU F.densityGraph.selected x.val.1) r).symm
        ⟨fun h => (congrFun h 0).symm,fun h => funext (fun i => by fin_cases i; exact h.symm)⟩)
  have hDG : ∀ x : A, ∀ r w, RF.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ RF.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r (Fin.last b) := by
    intro x r w
    exact (gammaSelectedVolumeSchema_density V hV G.densityGraph.selected (Fin.last b)
      (fun q hq => G.densityGraph_label_nonzero q hq) x.val.1 r w).trans
      (and_congr (Set.ext_iff.mp (gammaSelectedLabelSchema_domain V hV G.densityGraph.selected x.val.1) r).symm
        ⟨fun h => (congrFun h 0).symm,fun h => funext (fun i => by fin_cases i; exact h.symm)⟩)
  exact gamma_unary_fibrewise_volume_comparison_without_field hc C C₀ hCC₀ C.uncountable.le C.saturated C.model00 C.small hΞ
    γ hγ hγ1 (Set.Subset.refl _) A hA LF RF F.densityGraph.selected G.densityGraph.selected
    (Fin.last a) (Fin.last b) (fun x => hNF x.val.1) (fun x => hNG x.val.1)
    (fun x => gammaSelectedLabelSchema_labels U hU F.densityGraph.selected x.val)
    (fun x => gammaSelectedLabelSchema_labels V hV G.densityGraph.selected x.val) hDF hDG
    (fun x => selected_densityGraph_named_common hc Ξ F G NF NG x.val.1 (hCommon x.val.1))
    U V hU hV (gammaSelectedLabelSchema_source U hU F.densityGraph.selected)
    (gammaSelectedLabelSchema_source V hV G.densityGraph.selected)
    F.densityGraph.finite_selected G.densityGraph.finite_selected T E hT hE
    (F.densityGraph.form.restrict (fun _ h => h)) (G.densityGraph.form.restrict (fun _ h => h))
    (fun q => F.densityGraph_form_last ⟨q.val,q.property⟩)
    (fun q => G.densityGraph_form_last ⟨q.val,q.property⟩)

end IntegrationInACVF.Section7
