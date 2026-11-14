import Integration7.GammaUnaryRawVolumeComparison
import Integration7.HeadFibreRawVolumeContexts
import Integration7.HeadVolumeParameterContexts
import Integration7.SelectedVolumeHeadPointwiseWitnesses
import Integration7.MixedRetainedLabelVolumeForms

/-! Contracting one actual VF head on both sides preserves the original
fibrewise Gamma common-volume-blowup hypothesis. -/

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
variable {B : Base (M := M)} {S : Set M} {n a b k : ℕ}

private theorem retained_density_row
    (U : DefSet (M := M) S 1 a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a) (δ : Fin a) (hδ : ∀ q ∈ carrier U, (q.2 δ).val ≠ iRVZero)
    (z : Point (M := M) 1 0) (r : Fin a → RV (M := M)) (w : Fin 1 → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).rowDensity (rawVFParameter z) r w ↔
      r ∈ (gammaSelectedLabelSchema U hU ρ).rowDomain (rawVFParameter z) ∧ w 0 = r δ := by
  exact (gammaSelectedVolumeSchema_density U hU ρ δ hδ z.1 r w).trans
    (and_congr (Set.ext_iff.mp (gammaSelectedLabelSchema_domain U hU ρ z.1) r).symm
      ⟨fun h => (congrFun h 0).symm,fun h => funext (fun i => by fin_cases i;exact h.symm)⟩)

set_option maxHeartbeats 3200000 in
theorem gamma_head_volume_common_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b) (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hfinU : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    (hCommon : ∀ x : Fin (n+1) → VF (M := M),
      (gammaSelectedVolumeSchema U hU ρ δ).commonByGammaGeometry
        (gammaSelectedVolumeSchema V hV τ ε) (fun j => (x j).val))
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M)) :
    (gammaSelectedVolumeSchema T.contractedSet (gamma_headImage T.target hTarget) (headAppendVolumeIndex T ρ)
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).commonByGammaGeometry
      (gammaSelectedVolumeSchema E.contractedSet (gamma_headImage E.target hETarget) (headAppendVolumeIndex E τ)
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))) (fun j => (x j).val) := by
  let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have hsmall : Cardinal.mk Bx.real < κ := small_union_range hκ B.real hreal (fun j => (x j).val)
  let D₀ := headVolumeParameterContext C x
  let hRD := head_volume_context_contains_fibre_base C x
  let hBD := head_volume_context_contains_original_base C hBC x
  let Ux := coordinateFibre U 0 (headFrozenTuple x)
  let Vx := coordinateFibre V 0 (headFrozenTuple x)
  have hUx := gamma_head_fibre U hU x
  have hVx := gamma_head_fibre V hV x
  have hδx : ∀ p ∈ carrier Ux, (p.2 δ).val ≠ iRVZero :=
    fun p hp => hδ (coordinateInsert 0 (headFrozenTuple x) p) hp
  have hεx : ∀ p ∈ carrier Vx, (p.2 ε).val ≠ iRVZero :=
    fun p hp => hε (coordinateInsert 0 (headFrozenTuple x) p) hp
  have hfinUx := headFibre_selected_finite U ρ hfinU x
  have hfinVx := headFibre_selected_finite V τ hfinV x
  let UD := extendBase Ux hRD
  let VD := extendBase Vx hRD
  let TD := (headCoordinateFibreContraction T x).extendBase hRD
  let ED := (headCoordinateFibreContraction E x).extendBase hRD
  have hTD := (headCoordinateFibreContraction T x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction T hT hTarget x)
  have hED := (headCoordinateFibreContraction E x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction E hE hETarget x)
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound hκ hs hsmall hgamma Ux hUx ρ δ hδx hfinUx
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound hκ hs hsmall hgamma Vx hVx τ ε hεx hfinVx
  let F := (gammaSelectedVolumeSchema Ux hUx ρ δ).withBound NF
  let G := (gammaSelectedVolumeSchema Vx hVx τ ε).withBound NG
  have hWitness := selected_volume_head_formula_witnesses hc hκ hs h00 hreal hgamma U V hU hV ρ τ δ ε
    hδ hε hCommon x NF NG hNF hNG
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists T.contractedSet (gamma_headImage T.target hTarget)
    (headAppendVolumeIndex T ρ) (head_append_selected_fibres_finite hκ hs hreal T hT hTarget ρ hfinU) x
  obtain ⟨Q⟩ := selectedLabelFibrePresentation_exists E.contractedSet (gamma_headImage E.target hETarget)
    (headAppendVolumeIndex E τ) (head_append_selected_fibres_finite hκ hs hreal E hE hETarget τ hfinV) x
  obtain ⟨C₁,hD₀C₁,hPC₁⟩ := finiteVolumePresentationContainingContext D₀ P hBD
  obtain ⟨C₀,hC₁C₀,hQC₀⟩ := finiteVolumePresentationContainingContext C₁ Q (hBD.trans hD₀C₁)
  let hD₀C₀ := hD₀C₁.trans hC₁C₀
  let A := PresentedSet.univ (pointSpace (M := M) 1 0) (D₀.base : Set M)
  have hA : GammaSetDefinable Bx (carrier A) :=
    (gammaLogicInput Bx).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 1 0) Bx.real))
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc UD) δ (fun q => hδx q.val q.property)
  let η := mixedRetainedLabelVolumeForm (rawSpecialSet hc VD) ε (fun q => hεx q.val q.property)
  obtain ⟨hWU,hWV,D₁,hC₀D₁,hWD₁,hZD₁,hRaw⟩ := gamma_unary_raw_volume_comparison_with_geometry
    hc D₀ C₀ hD₀C₀ hκ hs h00 hsmall hgamma γ hγ hγ1 hBD A hA F G ρ τ δ ε
    (fun z => hNF z.val.1) (fun z => hNG z.val.1)
    (fun z => gammaSelectedLabelSchema_labels Ux hUx ρ z.val)
    (fun z => gammaSelectedLabelSchema_labels Vx hVx τ z.val)
    (fun z => retained_density_row Ux hUx ρ δ hδx z.val)
    (fun z => retained_density_row Vx hVx τ ε hεx z.val)
    (fun z => hWitness z.val.1) UD VD hUx hVx
    (gammaSelectedLabelSchema_source Ux hUx ρ) (gammaSelectedLabelSchema_source Vx hVx τ)
    hfinUx hfinVx TD ED hTD hED ω η (fun _ => rfl) (fun _ => rfl)
  let hD₀D₁ := hD₀C₀.trans hC₀D₁
  let hPD₁ := hPC₁.trans (hC₁C₀.trans hC₀D₁)
  let hQD₁ := hQC₀.trans hC₀D₁
  obtain ⟨D₂,hD₁D₂,eP,heP⟩ := head_fibre_raw_volume_context_iso hc C D₀ D₁ hκ hs hreal hBC
    U hU ρ hfinU T hT hTarget δ hδ x hRD hD₀D₁ P hPD₁ hWU
  let hD₀D₂ := hD₀D₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,eQ,heQ⟩ := head_fibre_raw_volume_context_iso hc C D₀ D₂ hκ hs hreal hBC
    V hV τ hfinV E hE hETarget ε hε x hRD hD₀D₂ Q (hQD₁.trans hD₁D₂) hWV
  let hD₁D₃ := hD₁D₂.trans hD₂D₃
  let hPD₃ := hPD₁.trans hD₁D₃
  let hQD₃ := hQD₁.trans hD₁D₃
  let AP := gammaCoordinateDensityObject (e := k+1) (k := 0) hc D₃ P.toGamma hPD₃ _
    (selected_fibre_retained_density_nonzero T.contractedSet (headAppendVolumeIndex T ρ) _
      (head_retained_density_nonzero T δ hδ) x P)
  let AQ := gammaCoordinateDensityObject (e := k+1) (k := 0) hc D₃ Q.toGamma hQD₃ _
    (selected_fibre_retained_density_nonzero E.contractedSet (headAppendVolumeIndex E τ) _
      (head_retained_density_nonzero E ε hε) x Q)
  have hAP : VolumeObjectGamma AP Bx := gamma_coordinate_density_object_graphs hc D₃ P.toGamma hPD₃ _ _
  have hAQ : VolumeObjectGamma AQ Bx := gamma_coordinate_density_object_graphs hc D₃ Q.toGamma hQD₃ _ _
  have hHead : GammaVolumeBlowupEquivalent Bx (D₃.base : Set M) (k+1) ⟨AP,hAP⟩ ⟨AQ,hAQ⟩ := by
    refine GammaVolumeBlowupEquivalent.trans hc D₃ Bx ?_ ((hRaw.extend hD₁D₃).trans hc D₃ Bx ?_)
    · exact .of_iso D₃ Bx (eP.extend hD₂D₃) (heP.extend hD₂D₃)
    · exact .of_iso D₃ Bx (eQ.symm hc D₃) (heQ.symm hc D₃ Bx)
  exact ⟨D₃,⟨AP,hAP⟩,⟨AQ,hAQ⟩,rfl,rfl,
    selected_coordinate_density_schema_row hc D₃ T.contractedSet (gamma_headImage T.target hTarget)
      (headAppendVolumeIndex T ρ) _ (head_retained_density_nonzero T δ hδ) x P hPD₃,
    selected_coordinate_density_schema_row hc D₃ E.contractedSet (gamma_headImage E.target hETarget)
      (headAppendVolumeIndex E τ) _ (head_retained_density_nonzero E ε hε) x Q hQD₃,hHead⟩

end IntegrationInACVF.Section7
