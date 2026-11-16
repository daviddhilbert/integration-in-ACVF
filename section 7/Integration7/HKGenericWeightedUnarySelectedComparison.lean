import Integration7.HKWeightedUnaryComparisonFromPreparation
import Integration7.EmptySelectedContractionExtensionCharts

/-! Generic exact-density row isomorphisms compare specified unary
selected contractions with no old volume coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b : ℕ}

set_option maxHeartbeats 3200000 in
theorem weighted_unary_comparison_from_generic_geometry {κ : Cardinal}
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
    (δ : Fin a) (ε : Fin b)
    (hWitness : ∀ x : Fin 1 → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      ∃ H : GammaRelationFormula B 1 a b (fun _ => .vf),
        H.val ⊆ densityLabelConstraint (fun _ => .vf) δ ε ∧
          (gammaFiniteRowChartSchema F G H).valid (vfValues x))
    (U : DefSet (M := M) (C.base : Set M) 1 a) (V : DefSet (M := M) (C.base : Set M) 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hSourceU : carrier U = vfSchemaSource (carrier A) F) (hSourceV : carrier V = vfSchemaSource (carrier A) G)
    (hfinU : ∀ (x : Fin 1 → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ Fin.elim0 = t}.Finite)
    (hfinV : ∀ (x : Fin 1 → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin b → RV (M := M) | (x,r) ∈ carrier V ∧ r ∘ Fin.elim0 = t}.Finite)
    {σ τ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (E : StandardContraction V τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε) :
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
  let A₀ := SpecialTransformations.Section5.extendBase A hCC₀
  obtain ⟨C₁,hC₀C₁,hPreparation⟩ := generic_weighted_comparison_preparation
    hc hκ hs hreal hgamma C₀ (hBC.trans hCC₀) A₀ hA F G
      (fun x => hF ⟨x.val,x.property⟩) (fun x => hG ⟨x.val,x.property⟩) δ ε hWitness
  let hCC₁ := hCC₀.trans hC₀C₁
  let U₁ := SpecialTransformations.Section5.extendBase U hCC₁
  let V₁ := SpecialTransformations.Section5.extendBase V hCC₁
  let T₁ := T.extendBase hCC₁
  let E₁ := E.extendBase hCC₁
  have hT₁ : GammaProgramDefinable B T₁.program := T.program.extendBase_gamma hCC₁ hT
  have hE₁ : GammaProgramDefinable B E₁.program := E.program.extendBase_gamma hCC₁ hE
  obtain ⟨hRU₁,hRV₁,D,hC₁D,hRD,hVD,hComparison⟩ :=
    weighted_unary_comparison_from_preparation hc C₁ C₁ (Set.Subset.refl _)
      hκ hs hreal hgamma γ hγ hγ1 (hBC.trans hCC₁)
      (SpecialTransformations.Section5.extendBase A hCC₁) hA F G
      (fun x => hLF ⟨x.val,x.property⟩) (fun x => hLG ⟨x.val,x.property⟩) δ ε hPreparation
      U₁ V₁ hU hV hSourceU hSourceV hfinU hfinV T₁ E₁ hT₁ hE₁
      (ω.extend hCC₁) (π.extend hCC₁)
      (fun q => hω ⟨q.val,q.property⟩) (fun q => hπ ⟨q.val,q.property⟩)
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
  let eT := emptySelectedContractionExtensionVolumeIso (n := 0) hc C C₁ D hCC₁ hC₁D
    hκ hs hreal hBC U hU Fin.elim0 hfinU T hT δ hδU
  let eE := emptySelectedContractionExtensionVolumeIso (n := 0) hc C C₁ D hCC₁ hC₁D
    hκ hs hreal hBC V hV Fin.elim0 hfinV E hE ε hεV
  have heT := gamma_empty_selected_contraction_extension_iso (n := 0) hc C C₁ D hCC₁ hC₁D
    hκ hs hreal hBC U hU Fin.elim0 hfinU T hT δ hδU
  have heE := gamma_empty_selected_contraction_extension_iso (n := 0) hc C C₁ D hCC₁ hC₁D
    hκ hs hreal hBC V hV Fin.elim0 hfinV E hE ε hεV
  exact ⟨normalized_contraction_retained_density_nonzero T δ hδU,
    normalized_contraction_retained_density_nonzero E ε hεV,D,hC₀C₁.trans hC₁D,
    hCC₁.trans hC₁D,hCC₁.trans hC₁D,
    ((GammaVolumeBlowupEquivalent.of_iso D B eT heT).trans hc D B hComparison).trans hc D B
      (GammaVolumeBlowupEquivalent.of_iso D B (eE.symm hc D) (heE.symm hc D B))⟩

end IntegrationInACVF.Section7.HK
