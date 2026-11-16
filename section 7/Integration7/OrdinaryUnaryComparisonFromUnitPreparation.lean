module

public import Integration7.PreparedOrdinaryUnitComparisons
public import Integration7.PreparedOrdinaryUnitVolumeCharts
public import Integration7.GammaOrdinaryUnaryPreparedVolumeComparison

@[expose] public section

/-! A constructed ordinary preparation compares two specified unary
contractions with retained unit density, keeping original-Gamma geometry. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem gamma_ordinary_unary_comparison_from_unit_preparation {κ : Cardinal}
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
    (hPreparation : HasPreparedOrdinaryUnitComparison hc A F G)
    (U : DefSet (M := M) (C.base : Set M) 1 a) (V : DefSet (M := M) (C.base : Set M) 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hSourceU : carrier U = vfSchemaSource (carrier A) F) (hSourceV : carrier V = vfSchemaSource (carrier A) G)
    (hfinU : ∀ (x : Fin 1 → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ Fin.elim0 = t}.Finite)
    (hfinV : ∀ (x : Fin 1 → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ Fin.elim0 = t}.Finite)
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (δ : Fin a) (ε : Fin b) (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hUnitU : ∀ q : U, (q.val.2 δ).val = iRVOne) (hUnitV : ∀ q : V, (q.val.2 ε).val = iRVOne) :
    let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU (Fin.elim0 : Fin 0 → Fin a) hfinU T hT
    let RV := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hV (Fin.elim0 : Fin 0 → Fin b) hfinV E hE
    ∃ hRU : ∀ u : rvObjectDomain RU.object, (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object, (u.val (FiniteRV.contractionOldLabelIndex E ε)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      GammaVolumeBlowupEquivalent B (D.base : Set M) 0
        ⟨gammaCoordinateDensityObject (e := 0) (k := 0) hc D RU hRD (FiniteRV.contractionOldLabelIndex T δ) hRU,
          gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D RU hRD _ hRU⟩
        ⟨gammaCoordinateDensityObject (e := 0) (k := 0) hc D RV hVD (FiniteRV.contractionOldLabelIndex E ε) hRV,
          gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc D RV hVD _ hRV⟩ := by
  intro RU RV
  obtain ⟨l,Z,K,hK,hZ,BP,hFA,hGA,hDF,hDG,hPrepared⟩ := hPreparation
  let D := GammaParameterRecode.prepared K hK
  let PF := D.object F
  let QG := D.object G
  let P := PF.indexedPresentation BP hDF
  let Q := QG.indexedPresentation BP hDG
  let eK : GammaIso B (carrier A) (carrier Z) :=
    ⟨K.equiv,GammaChainDefinable.graph (gammaLogicInput B) K.chain hK⟩
  obtain ⟨C₁,hC₀C₁,hBP₁⟩ := finiteVolumePresentationContainingContext C₀ BP (hBC.trans hCC₀)
  let hCC₁ := hCC₀.trans hC₀C₁
  obtain ⟨hRU,hP,D₁,hC₁D₁,hRD₁,hPD₁,hLeft⟩ :=
    gamma_ordinary_unary_prepared_volume_comparison_with_geometry hc C hκ hs hreal hgamma γ hγ hγ1 hBC C₁ hCC₁
      A Z K hK hA hZ F PF Fin.elim0 hFA BP
      (fun t ht => PF.finiteRow_of_valid _ (hDF t ht))
      (prepared_selected_rows Z eK F PF Fin.elim0 hFA hLF) P U hU hSourceU hfinU T hT δ ω hω
  let hCD₁ := hCC₁.trans hC₁D₁
  obtain ⟨hRV,hQ,D₂,hD₁D₂,hVD₂,hQD₂,hRight⟩ :=
    gamma_ordinary_unary_prepared_volume_comparison_with_geometry hc C hκ hs hreal hgamma γ hγ hγ1 hBC D₁ hCD₁
      A Z K hK hA hZ G QG Fin.elim0 hGA BP
      (fun t ht => QG.finiteRow_of_valid _ (hDG t ht))
      (prepared_selected_rows Z eK G QG Fin.elim0 hGA hLG) Q V hV hSourceV hfinV E hE ε π hπ
  let hPD₂ := hPD₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,g,hg⟩ := hPrepared D₂ P Q hPD₂ hQD₂ (hBC.trans (hCD₁.trans hD₁D₂))
  let hPD₃ := hPD₂.trans hD₂D₃
  let hQD₃ := hQD₂.trans hD₂D₃
  obtain ⟨gP,hgP⟩ := prepared_ordinary_unit_volume_chart hc D₃ A Z K F PF hFA BP P U hSourceU δ hUnitU hPD₃ hP
  obtain ⟨gQ,hgQ⟩ := prepared_ordinary_unit_volume_chart hc D₃ A Z K G QG hGA BP Q V hSourceV ε hUnitV hQD₃ hQ
  let gMid := (gP.trans hc D₃ g).trans hc D₃ (gQ.symm hc D₃)
  have hMid := (hgP.trans hc D₃ B hg).trans hc D₃ B (hgQ.symm hc D₃ B)
  let hD₁D₃ := hD₁D₂.trans hD₂D₃
  exact ⟨hRU,hRV,D₃,hC₀C₁.trans (hC₁D₁.trans hD₁D₃),hRD₁.trans hD₁D₃,hVD₂.trans hD₂D₃,
    (hLeft.extend hD₁D₃).trans hc D₃ B
      ((GammaVolumeBlowupEquivalent.of_iso D₃ B gMid hMid).trans hc D₃ B ((hRight.extend hD₂D₃).symm hc D₃ B))⟩

end IntegrationInACVF.Section7
