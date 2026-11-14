import Integration7.UnaryPreparedVolumeSliceWitness
import Integration7.ContractionRetainedDensityLabels
import Integration7.PreparedIndexedRetainedLabels
import Integration7.VolumeSliceCommonUniformity
/-! An arbitrary unary standard contraction is compared with its prepared
indexed family by actual common volume blowups. All RV-prefix slices
have constructed original-Gamma formula witnesses, then glue uniformly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a l k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

set_option maxHeartbeats 2400000 in
theorem gamma_unary_prepared_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ) (FBase : VFFieldBase B.real)
    (hBC : B.real ⊆ (C.base : Set M))
    (C₀ : BaseContext M) (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 0)
    (Z : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 l)
    (K : SpecialBijection A Z) (hK : GammaChainDefinable B K.chain)
    (hA : GammaSetDefinable B (carrier A)) (hZ : IsRVPullback (carrier Z))
    (F : GammaFiniteRVSchema B 1 a (k+1)) (G : GammaFiniteRVSchema B (1+l) a (k+1) (fun _ => .rv))
    (ρ : Fin (k+1) → Fin a)
    (hRows : ∀ q : Z, GammaSchemaRowAgreement F (rawVFParameter (K.inverseMap q).val) G (rawPreparedKey q.val))
    (BP : PreparedIndexPresentation B Z)
    (hG : ∀ s ∈ preparedKeyDomain Z, G.finiteRow (rvValues s))
    (hLabels : ∀ s ∈ preparedKeyDomain Z, ∀ r y, G.rowVolume (rvValues s) r y ↔
      r ∈ G.rowDomain (rvValues s) ∧ r ∘ ρ = y)
    (J : G.IndexedPresentation BP)
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 1 a)
    (hU : GammaSetDefinable B (carrier U)) (hSource : carrier U = vfSchemaSource (carrier A) F)
    (hfin : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (ω : VolumeForm (rawSpecialSet hc U)) (hDensity : ∀ q, ω.value q = q.val.2 δ) :
    let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT
    let RV := gammaSwapVolumeBlocks J.toGamma
    ∃ hRU : ∀ u : rvObjectDomain RU.object,
        (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero,
    ∃ hRV : ∀ u : rvObjectDomain RV.object, (u.val (Fin.natAdd (1+l) δ)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hCD : (C₀.base : Set M) ⊆ (D.base : Set M),
    ∃ hRD : RU.codes ⊆ (D.base : Set M), ∃ hVD : RV.codes ⊆ (D.base : Set M),
      VolumeBlowupEquivalent
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RU hRD (FiniteRV.contractionOldLabelIndex T δ) hRU)
        (gammaCoordinateDensityObject (e := k+1) (k := 0) hc D RV hVD (Fin.natAdd (1+l) δ) hRV) := by
  intro RU RW
  have hδU : ∀ q : U, (q.val.2 δ).val ≠ iRVZero := by
    intro q
    apply (rv_nonzero_iff_raw _).mp
    intro hz
    exact ω.nonzero q ((hDensity q).trans hz)
  have hRU : ∀ u : rvObjectDomain RU.object,
      (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero :=
    normalized_contraction_retained_density_nonzero T δ hδU
  have hRV : ∀ u : rvObjectDomain RW.object, (u.val (Fin.natAdd (1+l) δ)).val ≠ iRVZero :=
    prepared_indexed_retained_label_nonzero A Z K F G hRows BP J U hSource δ hδU
  obtain ⟨C₁,hC₀C₁,hJC₁⟩ := finiteVolumePresentationContainingContext C₀ J (hBC.trans hCC₀)
  let hCC₁ := hCC₀.trans hC₀C₁
  have hR₁ : RU.codes ⊆ (C₁.base : Set M) := hCC₁
  have hV₁ : RW.codes ⊆ (C₁.base : Set M) := hJC₁
  obtain ⟨NF,hNF⟩ := gammaVolumeSliceDensitySchema_uniform_bound hκ hs hreal hgamma RU _ hRU
  obtain ⟨NG,hNG⟩ := gammaVolumeSliceDensitySchema_uniform_bound hκ hs hreal hgamma RW _ hRV
  have hWitness : ∀ t : Fin (k+1) → RV (M := M),
      ∃ H : GammaVolumeCommonSchema ((gammaVolumeSliceDensitySchema RU (FiniteRV.contractionOldLabelIndex T δ)).withBound NF)
        ((gammaVolumeSliceDensitySchema RW (Fin.natAdd (1+l) δ)).withBound NG), H.valid (rvValues t) := by
    intro t
    let LF := (gammaVolumeSliceDensitySchema RU (FiniteRV.contractionOldLabelIndex T δ)).withBound NF
    let RF := (gammaVolumeSliceDensitySchema RW (Fin.natAdd (1+l) δ)).withBound NG
    obtain ⟨P⟩ := LF.realize (rvValues t) (hNF t)
    obtain ⟨Q⟩ := RF.realize (rvValues t) (hNG t)
    have hPδ : ∀ u : P.finite.domain,
        (u.val (FiniteRV.contractionOldLabelIndex T δ)).val ≠ iRVZero := by
      intro u
      obtain ⟨v,hv,_⟩ := (gammaVolumeSliceSchema_domain RU t u.val).mp (P.finite.domain_eq.le u.property)
      exact fun hz => hRU v ((congrArg (fun r => (r (FiniteRV.contractionOldLabelIndex T δ)).val) hv).trans hz)
    have hQδ : ∀ u : Q.finite.domain, (u.val (Fin.natAdd (1+l) δ)).val ≠ iRVZero := by
      intro u
      obtain ⟨v,hv,_⟩ := (gammaVolumeSliceSchema_domain RW t u.val).mp (Q.finite.domain_eq.le u.property)
      exact fun hz => hRV v ((congrArg (fun r => (r (Fin.natAdd (1+l) δ)).val) hv).trans hz)
    let Ct := finiteVolumeParameterContext C₁ (Set.range (rvValues t)) (Set.finite_range _)
    have hC₁t : (C₁.base : Set M) ⊆ (Ct.base : Set M) :=
      fun _ hx => finiteVolumeParameterContext_contains C₁ _ (Set.finite_range _) (Or.inl hx)
    have hBt : B.real ∪ Set.range (rvValues t) ⊆ (Ct.base : Set M) := by
      rintro x (hx | hx)
      · exact hC₁t (hCC₁ (hBC hx))
      · exact finiteVolumeParameterContext_contains C₁ _ (Set.finite_range _) (Or.inr hx)
    obtain ⟨C₂,hCt₂,hP₂⟩ := P.exists_containingContext Ct hBt
    obtain ⟨C₃,hC₂₃,hQ₃⟩ := Q.exists_containingContext C₂ (hBt.trans hCt₂)
    let hCC₃ := hCC₁.trans (hC₁t.trans (hCt₂.trans hC₂₃))
    have PL := gamma_label_density_coordinate_row hc C₃ LF (rvValues t) (hNF t) P (hP₂.trans hC₂₃)
      (FiniteRV.contractionOldLabelIndex T δ)
      (gammaVolumeSliceDensitySchema_row RU _ hRU t) hPδ
    have PR := gamma_label_density_coordinate_row hc C₃ RF (rvValues t) (hNG t) Q hQ₃
      (Fin.natAdd (1+l) δ) (gammaVolumeSliceDensitySchema_row RW _ hRV t) hQδ
    exact gamma_unary_prepared_volume_slice_witness hc C C₃ hCC₃ hκ hs hreal hgamma γ hγ hγ1 FBase hBC
      A Z K hK hA hZ F G ρ hRows BP hG hLabels J U hU hSource hfin T hT δ ω hDensity t
      P.finite Q.finite (hP₂.trans hC₂₃) hQ₃ hPδ hQδ LF RF (hNF t) (hNG t) PL PR
  obtain ⟨D,hC₁D,h⟩ := gamma_volume_slice_density_common_uniformity hc hκ hs hreal hgamma C₁
    RU RW hR₁ hV₁ (FiniteRV.contractionOldLabelIndex T δ) (Fin.natAdd (1+l) δ) hRU hRV NF NG hWitness
  exact ⟨hRU,hRV,D,hC₀C₁.trans hC₁D,hR₁.trans hC₁D,hV₁.trans hC₁D,h⟩

end IntegrationInACVF.Section7
