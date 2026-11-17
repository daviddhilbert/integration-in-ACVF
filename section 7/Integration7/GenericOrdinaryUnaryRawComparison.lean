module

public import Integration7.GenericOrdinaryUnarySelectedComparison
public import Integration7.EmptySelectedUnaryVolumeCharts

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Generic isomorphisms of ordinary rows give common forward blowups of
both specified raw unary finite contractions, with original-Gamma geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_ordinary_unary_raw_comparison_from_generic_geometry {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) 1 0) (hA : GammaSetDefinable B (carrier A))
    (F : GammaFiniteRVSchema B 1 a 0) (G : GammaFiniteRVSchema B 1 b 0)
    (hLF : ∀ x : A, ∀ r y, F.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ F.rowDomain (rawVFParameter x.val) ∧ r ∘ (Fin.elim0 : Fin 0 → Fin a) = y)
    (hLG : ∀ x : A, ∀ r y, G.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ G.rowDomain (rawVFParameter x.val) ∧ r ∘ (Fin.elim0 : Fin 0 → Fin b) = y)
    (hF : ∀ x : A, F.valid (rawVFParameter x.val))
    (hG : ∀ x : A, G.valid (rawVFParameter x.val))
    (hWitness : ∀ x : Fin 1 → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B 1 a b (fun _ => .vf), (gammaFiniteRowChartSchema F G H).valid (vfValues x))
    (U : DefSet (M := M) (C.base : Set M) 1 a) (V : DefSet (M := M) (C.base : Set M) 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hSourceU : carrier U = vfSchemaSource (carrier A) F) (hSourceV : carrier V = vfSchemaSource (carrier A) G)
    (hfinU : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin 1 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (δ : Fin a) (ε : Fin b) (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hUnitU : ∀ q : U, (q.val.2 δ).val = iRVOne) (hUnitV : ∀ q : V, (q.val.2 ε).val = iRVOne) :
    let RU := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hU hfinU T hT
    let RV := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hV hfinV E hE
    ∃ hRU : ∀ u : rvObjectDomain RU.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object, (u.val (suffixIndex E.program.rvArity_le ε)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent B (D.base : Set M) 0
        ⟨gammaCoordinateDensityObject (e := 0) (k := 0) hc D RU hRD (suffixIndex T.program.rvArity_le δ) hRU,
          gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D RU hRD _ hRU⟩
        ⟨gammaCoordinateDensityObject (e := 0) (k := 0) hc D RV hVD (suffixIndex E.program.rvArity_le ε) hRV,
          gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D RV hVD _ hRV⟩ := by
  intro RU RV
  obtain ⟨hSU,hSV,D,hC₀D,hSD,hVD,hSelected⟩ :=
    gamma_ordinary_unary_comparison_from_generic_geometry hc C C₀ hCC₀ hκ hs hreal hgamma γ hγ hγ1 hBC
      A hA F G hLF hLG hF hG hWitness U V hU hV hSourceU hSourceV
      (empty_selected_volume_finite U hfinU) (empty_selected_volume_finite V hfinV)
      T E hT hE δ ε ω π hω hπ hUnitU hUnitV
  have hδU : ∀ q : U, (q.val.2 δ).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact ω.nonzero q ((hω q).trans hz)
  have hεV : ∀ q : V, (q.val.2 ε).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact π.nonzero q ((hπ q).trans hz)
  let hCD := hCC₀.trans hC₀D
  obtain ⟨hRU,D₁,hDD₁,fT,hfT⟩ := finite_contraction_normalization_volume_iso
    hc C D hCD hκ hs hreal hBC U hU hfinU T hT δ hδU
  obtain ⟨hRV,D₂,hD₁D₂,fE,hfE⟩ := finite_contraction_normalization_volume_iso
    hc C D₁ (hCD.trans hDD₁) hκ hs hreal hBC V hV hfinV E hE ε hεV
  let hDD₂ := hDD₁.trans hD₁D₂
  let hCD₂ := hCD.trans hDD₂
  obtain ⟨eT,heT⟩ := empty_selected_unary_volume_iso hc C D₂ hCD₂ hκ hs hreal hBC U hU hfinU T hT δ hδU
  obtain ⟨eE,heE⟩ := empty_selected_unary_volume_iso hc C D₂ hCD₂ hκ hs hreal hBC V hV hfinV E hE ε hεV
  let gT := (fT.extend hD₁D₂).trans hc D₂ (eT.symm hc D₂)
  have hgT := (hfT.extend hD₁D₂).trans hc D₂ B (heT.symm hc D₂ B)
  let gE := eE.trans hc D₂ (fE.symm hc D₂)
  have hgE := heE.trans hc D₂ B (hfE.symm hc D₂ B)
  refine ⟨hRU,hRV,D₂,hC₀D.trans hDD₂,hCD₂,hCD₂,
    GammaVolumeBlowupEquivalent.trans hc D₂ B ?_ ((hSelected.extend hDD₂).trans hc D₂ B ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D₂ B gT hgT
  · exact GammaVolumeBlowupEquivalent.of_iso D₂ B gE hgE

end IntegrationInACVF.Section7
