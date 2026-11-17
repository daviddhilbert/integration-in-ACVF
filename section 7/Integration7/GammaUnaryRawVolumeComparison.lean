module

public import Integration7.GammaUnaryVolumeComparisonFromFormulaWitnesses
public import Integration7.UnarySelectedNormalizationVolumeContexts
public import Integration7.GammaUnaryVolumeComparisonFromPreparation
public import Integration7.FormulaGammaVolumeUniformityContexts
public import Integration7.GammaSelectedContractionExtensionCharts
public import Integration7.UnaryVolumeComparisonFromPreparation
public import Integration7.FormulaVolumeUniformityContexts
public import Integration7.SelectedContractionExtensionVolumeIso
public import Integration7.GammaVFPreparedVolumeUniformity
public import Integration7.PreparedVolumeDensityRows
public import Integration7.IndexedVolumeCoordinateDensityIso
public import Integration7.GammaUnaryVolumeBlockSwap
public import Integration7.BlowupParameterExtension
public import IntegrationSection6.GammaUnaryPreparedContractionComparison

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The unary positive selected-family comparison from general formula
witnesses, with arbitrary existential exception parameters, over an arbitrary
real/Gamma base. A common preparation is constructed in a genuine small
context, and the unchanged original contraction objects are recovered
by their checked parameter-extension volume isomorphisms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_unary_raw_volume_comparison_with_geometry {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B 1 a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B 1 b k (fun _ => .vf))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b)
    (δ : Fin a) (ε : Fin b)
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hLF : ∀ x : A, ∀ r y, F.object.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ F.object.rowDomain (rawVFParameter x.val) ∧ r ∘ ρ = y)
    (hLG : ∀ x : A, ∀ r y, G.object.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ G.object.rowDomain (rawVFParameter x.val) ∧ r ∘ τ = y)
    (hDF : ∀ x : A, ∀ r w, F.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ F.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r δ)
    (hDG : ∀ x : A, ∀ r w, G.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ G.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r ε)
    (hWitness : ∀ x : A, ∃ H : GammaVolumeCommonSchema F G, H.valid (rawVFParameter x.val))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (V : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hSourceU : carrier U = vfSchemaSource (carrier A) F.object)
    (hSourceV : carrier V = vfSchemaSource (carrier A) G.object)
    (hfinU : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (hfinV : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ τ = t}.Finite)
    {σ υ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V υ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (ω : VolumeForm (rawSpecialSet hc U)) (η : VolumeForm (rawSpecialSet hc V))
    (hω : ∀ q, ω.value q = q.val.2 δ) (hη : ∀ q, η.value q = q.val.2 ε) :
    let RU := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs hreal hBC hU ρ hfinU T hT)
    let RV := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs hreal hBC hV τ hfinV E hE)
    ∃ hRU : ∀ u : rvObjectDomain RU.object,
        (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object,
        (u.val (suffixIndex E.program.rvArity_le ε)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent B (D.base : Set M) (k+1)
        ⟨gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RU hRD (suffixIndex T.program.rvArity_le δ) hRU,
          gamma_coordinate_density_object_graphs hc D RU hRD (suffixIndex T.program.rvArity_le δ) hRU⟩
        ⟨gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RV hVD (suffixIndex E.program.rvArity_le ε) hRV,
          gamma_coordinate_density_object_graphs hc D RV hVD (suffixIndex E.program.rvArity_le ε) hRV⟩ := by
  intro ZU ZV
  have hδU : ∀ q : U, (q.val.2 δ).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact ω.nonzero q ((hω q).trans hz)
  have hεV : ∀ q : V, (q.val.2 ε).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact η.nonzero q ((hη q).trans hz)
  obtain ⟨hRU,hRV,D₁,hC₀D₁,hRD₁,hVD₁,hComparison⟩ :=
    gamma_unary_volume_comparison_with_geometry hc C C₀ hCC₀ hκ hs h00 hreal hgamma γ hγ hγ1 hBC
      A hA F G ρ τ δ ε hF hG hLF hLG hDF hDG hWitness
      U V hU hV hSourceU hSourceV hfinU hfinV T E hT hE ω η hω hη
  let hCD₁ := hCC₀.trans hC₀D₁
  obtain ⟨hZU,D₂,hD₁D₂,eU,heU⟩ := unary_selected_normalization_volume_iso_in_context
    hc C D₁ hCD₁ hκ hs hreal hBC U hU ρ hfinU T hT δ hδU
  let hCD₂ := hCD₁.trans hD₁D₂
  obtain ⟨hZV,D₃,hD₂D₃,eV,heV⟩ := unary_selected_normalization_volume_iso_in_context
    hc C D₂ hCD₂ hκ hs hreal hBC V hV τ hfinV E hE ε hεV
  let hD₁D₃ := hD₁D₂.trans hD₂D₃
  let hCD₃ := hCD₁.trans hD₁D₃
  refine ⟨hZU,hZV,D₃,hC₀D₁.trans hD₁D₃,hCD₃,hCD₃,
    GammaVolumeBlowupEquivalent.trans hc D₃ B ?_ ((hComparison.extend hD₁D₃).trans hc D₃ B ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D₃ B (eU.extend hD₂D₃) (heU.extend hD₂D₃)
  · exact GammaVolumeBlowupEquivalent.of_iso D₃ B (eV.symm hc D₃) (heV.symm hc D₃ B)

end IntegrationInACVF.Section7
