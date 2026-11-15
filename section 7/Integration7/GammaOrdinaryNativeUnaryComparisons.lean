import Integration7.GenericOrdinaryUnaryRawComparison
import Integration7.GammaOrdinaryPointFormulaWitnesses
import Integration7.SelectedLabelSchemaUniformBounds

/-! Actual generic Gamma isomorphisms of finite ordinary native fibres
compare arbitrary specified raw unary contractions with retained unit density. -/
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
theorem gamma_ordinary_native_unary_raw_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) 1 a) (V : DefSet (M := M) (C.base : Set M) 1 b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin 1 → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (hWitness : ∀ x : Fin 1 → VFType (M := M), AlgebraicIndependent (vfParameterField B.real) x →
      Nonempty (GammaIso ⟨B.real ∪ Set.range (vfValues x),B.gamma⟩
        {q : Point (M := M) 0 a | (x,q.2) ∈ carrier U}
        {q : Point (M := M) 0 b | (x,q.2) ∈ carrier V}))
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
  let A := PresentedSet.univ (pointSpace (M := M) 1 0) (C.base : Set M)
  have hA : GammaSetDefinable B (carrier A) :=
    (gammaLogicInput B).real_set _ (setDefinable (PresentedSet.univ (pointSpace (M := M) 1 0) B.real))
  obtain ⟨NF,hNF⟩ := selected_label_schema_uniform_bound hκ hs hreal hgamma U hU
    (Fin.elim0 : Fin 0 → Fin a) (empty_selected_volume_finite U hfinU)
  obtain ⟨NG,hNG⟩ := selected_label_schema_uniform_bound hκ hs hreal hgamma V hV
    (Fin.elim0 : Fin 0 → Fin b) (empty_selected_volume_finite V hfinV)
  let F := (gammaSelectedLabelSchema U hU (Fin.elim0 : Fin 0 → Fin a)).withBound NF
  let G := (gammaSelectedLabelSchema V hV (Fin.elim0 : Fin 0 → Fin b)).withBound NG
  apply gamma_ordinary_unary_raw_comparison_from_generic_geometry hc C C₀ hCC₀ hκ hs hreal hgamma γ hγ hγ1 hBC
    A hA F G
    (fun x => gammaSelectedLabelSchema_labels U hU Fin.elim0 x.val)
    (fun x => gammaSelectedLabelSchema_labels V hV Fin.elim0 x.val)
    (fun x => hNF x.val.1) (fun x => hNG x.val.1) ?_
    U V hU hV (gammaSelectedLabelSchema_source U hU Fin.elim0) (gammaSelectedLabelSchema_source V hV Fin.elim0)
    hfinU hfinV T E hT hE δ ε ω π hω hπ hUnitU hUnitV
  intro x hx
  obtain ⟨e⟩ := hWitness x hx
  have hF : {q : Point (M := M) 0 a | (x,q.2) ∈ carrier U} =
      {q : Point (M := M) 0 a | q.2 ∈ F.rowDomain (vfValues x)} := by
    ext q
    exact (Set.ext_iff.mp (gammaSelectedLabelSchema_domain U hU (Fin.elim0 : Fin 0 → Fin a) x) q.2).symm
  have hG : {q : Point (M := M) 0 b | (x,q.2) ∈ carrier V} =
      {q : Point (M := M) 0 b | q.2 ∈ G.rowDomain (vfValues x)} := by
    ext q
    exact (Set.ext_iff.mp (gammaSelectedLabelSchema_domain V hV (Fin.elim0 : Fin 0 → Fin b) x) q.2).symm
  exact gamma_ordinary_point_formula_witness hκ hs hreal hgamma F G (vfValues x) (hNF x) (hNG x)
    (e.congr hF hG)

end IntegrationInACVF.Section7
