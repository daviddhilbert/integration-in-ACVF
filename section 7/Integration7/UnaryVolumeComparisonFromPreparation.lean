import Integration7.UnaryPreparedVolumeComparisonsWithoutField
import Integration7.GammaVFPreparedVolumeUniformity
import Integration7.PreparedVolumeDensityRows
import Integration7.IndexedVolumeCoordinateDensityIso
import Integration7.GammaUnaryVolumeBlockSwap
import Integration7.BlowupParameterExtension
import IntegrationSection6.GammaUnaryPreparedContractionComparison

/-! An actual simultaneous prepared volume comparison supplies the
unary two-contraction comparison over any real/Gamma base. The input
preparation is explicit; its construction in a small containing context
is provided separately, rather than assumed as an open geometric lemma. -/

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
theorem gamma_unary_fibrewise_volume_comparison_from_preparation {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0)
    (hA : GammaSetDefinable B (carrier A))
    (F : GammaRVVolumeSchema B 1 a k (fun _ => .vf))
    (G : GammaRVVolumeSchema B 1 b k (fun _ => .vf))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b)
    (δ : Fin a) (ε : Fin b)
    (hLF : ∀ x : A, ∀ r y, F.object.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ F.object.rowDomain (rawVFParameter x.val) ∧ r ∘ ρ = y)
    (hLG : ∀ x : A, ∀ r y, G.object.rowVolume (rawVFParameter x.val) r y ↔
      r ∈ G.object.rowDomain (rawVFParameter x.val) ∧ r ∘ τ = y)
    (hDF : ∀ x : A, ∀ r w, F.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ F.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r δ)
    (hDG : ∀ x : A, ∀ r w, G.rowDensity (rawVFParameter x.val) r w ↔
      r ∈ G.object.rowDomain (rawVFParameter x.val) ∧ w 0 = r ε)
    (hPreparation : HasPreparedVolumeCommonComparison hc A F G)
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
    let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfinU T hT
    let RV := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hV τ hfinV E hE
    ∃ hRU : ∀ u : rvObjectDomain RU.object,
        (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object,
        (u.val (FiniteRV.contractionOldLabelIndex E ε)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hC₀D : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RU hRD (FiniteRV.contractionOldLabelIndex T δ) hRU)
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RV hVD (FiniteRV.contractionOldLabelIndex E ε) hRV) := by
  intro RU RV
  obtain ⟨l,Z,K,hK,hZ,BP,hFA,hGA,hPF,hQG,hPrepared⟩ := hPreparation
  let D := GammaVolumeParameterRecode.prepared K hK
  let PF := D.volumeObject F
  let QG := D.volumeObject G
  have hRF : ∀ q : Z, GammaVolumeRowAgreement F (rawVFParameter (K.inverseMap q).val) PF (rawPreparedKey q.val) :=
    fun q => D.volumeObject_rows F _ _ (hFA q)
  have hRG : ∀ q : Z, GammaVolumeRowAgreement G (rawVFParameter (K.inverseMap q).val) QG (rawPreparedKey q.val) :=
    fun q => D.volumeObject_rows G _ _ (hGA q)
  let P := PF.indexedVolumePresentation BP hPF
  let Q := QG.indexedVolumePresentation BP hQG
  let eK : GammaIso B (carrier A) (carrier Z) :=
    ⟨K.equiv,GammaChainDefinable.graph (gammaLogicInput B) K.chain hK⟩
  have hPD := prepared_volume_density_rows A Z K F PF hRF δ hDF
  have hQD := prepared_volume_density_rows A Z K G QG hRG ε hDG
  obtain ⟨C₁,hC₀C₁,hBP₁⟩ := finiteVolumePresentationContainingContext C₀ BP (hBC.trans hCC₀)
  have hCC₁ := hCC₀.trans hC₀C₁
  obtain ⟨hRU,hP,D₁,hC₁D₁,hRD₁,hPD₁,hLeft⟩ :=
    gamma_unary_prepared_volume_comparison_without_field hc C hκ hs hreal hgamma γ hγ hγ1 hBC C₁ hCC₁
      A Z K hK hA hZ F.object PF.object ρ (fun q => (hRF q).1) BP
      (fun s hs => PF.object.finiteRow_of_valid _ (hPF s hs).1)
      (prepared_selected_rows Z eK F.object PF.object ρ (fun q => (hRF q).1) hLF)
      P.finite U hU hSourceU hfinU T hT δ ω hω
  have hCD₁ := hCC₁.trans hC₁D₁
  obtain ⟨hRV,hQ,D₂,hD₁D₂,hVD₂,hQD₂,hRight⟩ :=
    gamma_unary_prepared_volume_comparison_without_field hc C hκ hs hreal hgamma γ hγ hγ1 hBC D₁ hCD₁
      A Z K hK hA hZ G.object QG.object τ (fun q => (hRG q).1) BP
      (fun s hs => QG.object.finiteRow_of_valid _ (hQG s hs).1)
      (prepared_selected_rows Z eK G.object QG.object τ (fun q => (hRG q).1) hLG)
      Q.finite V hV hSourceV hfinV E hE ε η hη
  let hPD₂ := hPD₁.trans hD₁D₂
  obtain ⟨D₃,hD₂D₃,hPQ⟩ := hPrepared D₂ P Q hPD₂ hQD₂
    (hBP₁.trans (hC₁D₁.trans hD₁D₂)) (hBC.trans (hCD₁.trans hD₁D₂))
  let hPD₃ := hPD₂.trans hD₂D₃
  let hQD₃ := hQD₂.trans hD₂D₃
  let eP := indexedVolumeCoordinateDensityIso hc D₃ PF BP P hPD₃ δ hPD
  let eQ := indexedVolumeCoordinateDensityIso hc D₃ QG BP Q hQD₃ ε hQD
  have hPQ' := ((VolumeBlowupEquivalent.of_iso D₃ (eP.symm hc D₃)).trans hc D₃ hPQ).trans hc D₃
    (VolumeBlowupEquivalent.of_iso D₃ eQ)
  have hSwap := gamma_unary_volume_block_swap_common hc D₃ P.finite.toGamma Q.finite.toGamma
    hPD₃ hQD₃ (Fin.natAdd (1+l) δ) (Fin.natAdd (1+l) ε)
    (indexed_volume_presentation_density_nonzero PF BP P δ hPD)
    (indexed_volume_presentation_density_nonzero QG BP Q ε hQD) hPQ'
  let hD₁D₃ := hD₁D₂.trans hD₂D₃
  exact ⟨hRU,hRV,D₃,hC₀C₁.trans (hC₁D₁.trans hD₁D₃),hRD₁.trans hD₁D₃,hVD₂.trans hD₂D₃,
    ((hLeft.extend hD₁D₃).trans hc D₃ hSwap).trans hc D₃ ((hRight.extend hD₂D₃).symm hc D₃)⟩

end IntegrationInACVF.Section7
