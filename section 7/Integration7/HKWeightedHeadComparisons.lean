module

public import Integration7.HKWeightedNativeUnaryComparisons
public import Integration7.HKWeightedHeadFibreWitnesses
public import Integration7.HeadFiniteVolumeContexts
public import Integration7.HeadVolumeParameterContexts
public import Integration7.SelectedCoordinateDensityRows
public import Integration7.MixedRetainedLabelVolumeForms

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Exact-density generic row isomorphisms compare specified first-head
contractions through actual original-Gamma volume blowup geometry. -/
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

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem weighted_head_common_comparison_at_generic {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a)
    (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero)
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (hCommon : ∀ y : Fin (n+1) → VF (M := M), AlgebraicIndependent (vfParameterField B.real) y →
      ∃ e : GammaIso ⟨B.real ∪ Set.range (fun j => (y j).val),B.gamma⟩
        {q : Point (M := M) 0 a | (y,q.2) ∈ carrier U}
        {q : Point (M := M) 0 b | (y,q.2) ∈ carrier V},
        ∀ u, u.val.2 δ = (e.equiv u).val.2 ε)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x) :
    (gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).commonByGammaGeometry
      (gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
        (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
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
  have hfinUx := head_coordinate_fibre_finite_labels hfinU x
  have hfinVx := head_coordinate_fibre_finite_labels hfinV x
  let UD := extendBase Ux hRD
  let VD := extendBase Vx hRD
  let TD := (headCoordinateFibreContraction T x).extendBase hRD
  let ED := (headCoordinateFibreContraction E x).extendBase hRD
  have hTD := (headCoordinateFibreContraction T x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction T hT hTarget x)
  have hED := (headCoordinateFibreContraction E x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction E hE hETarget x)
  have hWitness := generic_head_weighted_row_iso U V δ ε hCommon x hx
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
    (head_selected_fibres_finite hκ hs hreal T hT hTarget Fin.elim0 (empty_selected_volume_finite U hfinU)) x
  obtain ⟨Q⟩ := selectedLabelFibrePresentation_exists E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
    (head_selected_fibres_finite hκ hs hreal E hE hETarget Fin.elim0 (empty_selected_volume_finite V hfinV)) x
  obtain ⟨C₁,hD₀C₁,hPC₁⟩ := finiteVolumePresentationContainingContext D₀ P hBD
  obtain ⟨C₀,hC₁C₀,hQC₀⟩ := finiteVolumePresentationContainingContext C₁ Q (hBD.trans hD₀C₁)
  let hD₀C₀ := hD₀C₁.trans hC₁C₀
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc UD) δ (fun q => hδx q.val q.property)
  let η := mixedRetainedLabelVolumeForm (rawSpecialSet hc VD) ε (fun q => hεx q.val q.property)
  obtain ⟨hWU,hWV,D₁,hC₀D₁,hWD₁,hZD₁,hRaw⟩ := weighted_native_unary_raw_comparison
    hc D₀ C₀ hD₀C₀ hκ hs hsmall hgamma γ hγ hγ1 hBD
    UD VD hUx hVx hfinUx hfinVx δ ε hWitness TD ED hTD hED ω η (fun _ => rfl) (fun _ => rfl)
  let hD₀D₁ := hD₀C₀.trans hC₀D₁
  let hPD₁ := hPC₁.trans (hC₁C₀.trans hC₀D₁)
  let hQD₁ := hQC₀.trans hC₀D₁
  obtain ⟨D₂,hD₁D₂,eP,heP⟩ := head_finite_volume_context_iso hc C D₀ D₁ hκ hs hreal hBC
    U hU hfinU T hT hTarget δ hδ x hRD hD₀D₁ P hPD₁ hWU
  let hD₀D₂ := hD₀D₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,eQ,heQ⟩ := head_finite_volume_context_iso hc C D₀ D₂ hκ hs hreal hBC
    V hV hfinV E hE hETarget ε hε x hRD hD₀D₂ Q (hQD₁.trans hD₁D₂) hWV
  let hD₁D₃ := hD₁D₂.trans hD₂D₃
  let hPD₃ := hPD₁.trans hD₁D₃
  let hQD₃ := hQD₁.trans hD₁D₃
  let AP := gammaCoordinateDensityObject (e := 0) (k := 0) hc D₃ P.toGamma hPD₃ _
    (selected_fibre_retained_density_nonzero (k := 0) T.contractedSet
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _ (head_retained_density_nonzero T δ hδ) x P)
  let AQ := gammaCoordinateDensityObject (e := 0) (k := 0) hc D₃ Q.toGamma hQD₃ _
    (selected_fibre_retained_density_nonzero (k := 0) E.contractedSet
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) _ (head_retained_density_nonzero E ε hε) x Q)
  have hAP : VolumeObjectGamma AP Bx := gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D₃ P.toGamma hPD₃ _ _
  have hAQ : VolumeObjectGamma AQ Bx := gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D₃ Q.toGamma hQD₃ _ _
  have hHead : GammaVolumeBlowupEquivalent Bx (D₃.base : Set M) 0 ⟨AP,hAP⟩ ⟨AQ,hAQ⟩ := by
    refine GammaVolumeBlowupEquivalent.trans hc D₃ Bx ?_ ((hRaw.extend hD₁D₃).trans hc D₃ Bx ?_)
    · exact .of_iso D₃ Bx (eP.extend hD₂D₃) (heP.extend hD₂D₃)
    · exact .of_iso D₃ Bx (eQ.symm hc D₃) (heQ.symm hc D₃ Bx)
  exact ⟨D₃,⟨AP,hAP⟩,⟨AQ,hAQ⟩,rfl,rfl,
    selected_coordinate_density_schema_row (k := 0) hc D₃ T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _ (head_retained_density_nonzero T δ hδ) x P hPD₃,
    selected_coordinate_density_schema_row (k := 0) hc D₃ E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) _ (head_retained_density_nonzero E ε hε) x Q hQD₃,hHead⟩

end IntegrationInACVF.Section7.HK
