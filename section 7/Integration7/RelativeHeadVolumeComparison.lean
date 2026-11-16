module

public import Integration7.UnaryRawFiniteVolumeComparison
public import Integration7.HeadFiniteVolumeContexts
public import Integration7.HeadVolumeParameterContexts
public import Integration7.RelativeVolumeFibreExceptions
public import IntegrationSection6.GammaRelativeHeadFibres

@[expose] public section

/-! The first head comparison in Corollary 7.6 on an actual frozen
fibre with its measure equation. Its sole selected volume coordinate is
the new head tag. Later coordinates can therefore use positive 7.5. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_relative_head_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (T : HeadPreparation U) (E : HeadPreparation V)
    (hT : GammaGraphDefinable B (pointMapGraph T.map)) (hE : GammaGraphDefinable B (pointMapGraph E.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (hETarget : GammaSetDefinable B (carrier E.target))
    (x : Fin n → VF (M := M))
    (hm : PreservesVFVolume
      (coordinateFibreRetainedVolumeForm hc U ω δ hω 0 (headFrozenTuple x))
      (coordinateFibreRetainedVolumeForm hc V π ε hπ 0 (headFrozenTuple x))
      (rawSpecialMap hc (coordinateFibreMap f 0 hi (headFrozenTuple x)))) :
    (gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))).commonByGammaGeometry
    (gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
      (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) ε))) (fun j => (x j).val) := by
  let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  let D₀ := headVolumeParameterContext C x
  let hRD := head_volume_context_contains_fibre_base C x
  let hBD := head_volume_context_contains_original_base C hBC x
  have hsmall := small_union_range hκ B.real hreal (fun j => (x j).val)
  let Ux := coordinateFibre U 0 (headFrozenTuple x)
  let Vx := coordinateFibre V 0 (headFrozenTuple x)
  let UD := extendBase Ux hRD
  let VD := extendBase Vx hRD
  let g₀ := coordinateFibreMap f 0 hi (headFrozenTuple x)
  let g : Map UD VD := @SpecialTransformations.DefinableGeometry.Map.extend LRV M
    (@CanonicalStructure.normalize M sM) _ _ _ _ Ux Vx g₀ hRD
  have hg : Function.Bijective g := coordinateFibreMap_bijective f hf 0 hi (headFrozenTuple x)
  have hgΓ : GammaGraphDefinable Bx (pointMapGraph g) := (gammaRelativeHeadFibreIso f hf hfΓ hi x).graph
  let TD := (headCoordinateFibreContraction T x).extendBase hRD
  let ED := (headCoordinateFibreContraction E x).extendBase hRD
  have hTD := (headCoordinateFibreContraction T x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction T hT hTarget x)
  have hED := (headCoordinateFibreContraction E x).program.extendBase_gamma hRD
    (gamma_head_coordinate_fibre_contraction E hE hETarget x)
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans h))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans h))
  have hfinU₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {r : Fin a → RV (M := M) | (y,r) ∈ carrier U ∧ r ∘ Fin.elim0 = t}.Finite :=
    (hfinU y).subset (fun _ h => h.1)
  have hfinV₀ (y : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)) :
      {r : Fin b → RV (M := M) | (y,r) ∈ carrier V ∧ r ∘ Fin.elim0 = t}.Finite :=
    (hfinV y).subset (fun _ h => h.1)
  obtain ⟨P⟩ := selectedLabelFibrePresentation_exists T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))
    (head_selected_fibres_finite hκ hs hreal T hT hTarget Fin.elim0 hfinU₀) x
  obtain ⟨Q⟩ := selectedLabelFibrePresentation_exists E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))
    (head_selected_fibres_finite hκ hs hreal E hE hETarget Fin.elim0 hfinV₀) x
  obtain ⟨C₁,hD₀C₁,hPC₁⟩ := finiteVolumePresentationContainingContext D₀ P hBD
  obtain ⟨C₀,hC₁C₀,hQC₀⟩ := finiteVolumePresentationContainingContext C₁ Q (hBD.trans hD₀C₁)
  let hD₀C₀ := hD₀C₁.trans hC₁C₀
  let Ω := (coordinateFibreRetainedVolumeForm hc U ω δ hω 0 (headFrozenTuple x)).extend hRD
  let ηD := (coordinateFibreRetainedVolumeForm hc V π ε hπ 0 (headFrozenTuple x)).extend hRD
  obtain ⟨hWU,hWV,D₁,hC₀D₁,hRaw⟩ := gamma_unary_raw_finite_volume_comparison
    (B₀ := Bx) hc D₀ C₀ hD₀C₀ hκ hs hsmall hgamma hBD γ hγ hγ1 UD VD
    (gamma_head_fibre U hU x) (gamma_head_fibre V hV x)
    (head_coordinate_fibre_finite_labels hfinU x) (head_coordinate_fibre_finite_labels hfinV x)
    g hg hgΓ Ω ηD δ ε (fun _ => rfl) (fun _ => rfl) (hm.extend hRD) TD ED hTD hED
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
    (selected_fibre_retained_density_nonzero (k := 0) T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _
      (head_retained_density_nonzero T δ hδ) x P)
  let AQ := gammaCoordinateDensityObject (e := 0) (k := 0) hc D₃ Q.toGamma hQD₃ _
    (selected_fibre_retained_density_nonzero (k := 0) E.contractedSet (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) _
      (head_retained_density_nonzero E ε hε) x Q)
  have hAP : VolumeObjectGamma AP Bx := gamma_coordinate_density_object_graphs (M := M) (B := Bx) (e := 0) (k := 0) hc D₃ P.toGamma hPD₃ _ _
  have hAQ : VolumeObjectGamma AQ Bx := gamma_coordinate_density_object_graphs (M := M) (B := Bx) (e := 0) (k := 0) hc D₃ Q.toGamma hQD₃ _ _
  have hHead : GammaVolumeBlowupEquivalent Bx (D₃.base : Set M) 0 ⟨AP,hAP⟩ ⟨AQ,hAQ⟩ := by
    refine GammaVolumeBlowupEquivalent.trans hc D₃ Bx ?_ ((hRaw.extend hD₁D₃).trans hc D₃ Bx ?_)
    · exact .of_iso D₃ Bx (eP.extend hD₂D₃) (heP.extend hD₂D₃)
    · exact .of_iso D₃ Bx (eQ.symm hc D₃) (heQ.symm hc D₃ Bx)
  exact ⟨D₃,⟨AP,hAP⟩,⟨AQ,hAQ⟩,rfl,rfl,
    selected_coordinate_density_schema_row (k := 0) hc D₃ T.contractedSet (gamma_headImage T.target hTarget)
      (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _ (head_retained_density_nonzero T δ hδ) x P hPD₃,
    selected_coordinate_density_schema_row (k := 0) hc D₃ E.contractedSet (gamma_headImage E.target hETarget)
      (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)) _ (head_retained_density_nonzero E ε hε) x Q hQD₃,hHead⟩

end IntegrationInACVF.Section7
