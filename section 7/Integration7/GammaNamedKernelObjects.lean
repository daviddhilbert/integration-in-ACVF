import Integration7.GammaNamedCodeContexts
import Integration7.RawStandardVolumeNormalization
import Integration7.RetainedSameOrderCommonContexts
import Integration7.SelectedStandardVolumeObjects
import Integration7.GammaVolumeSliceAssemblyGeometry
import Integration7.GammaRealRVMaps

/-! Gamma-named versions of the Gamma certificates and comparisons of the
literal contraction volume objects used by the Proposition 7.8 kernel. The
volume objects themselves are the original ones; they do not depend on the
Gamma base (the original `Ξ` argument only enters proofs). The Gamma base `G` is arbitrary with real part in
the code context `C`; Gamma-definability of the input domain and contraction
program is a hypothesis instead of being derived from definability over
`C.base`. The original lemmas are the case `G = ⟨C.base, Ξ⟩`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5

namespace IntegrationInACVF.Section7.GammaNamed
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a d k : ℕ}

theorem native_coordinate_density_volume_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (G : Base (M := M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) 0 a)
    (hU : GammaSetDefinable G (carrier U))
    (ι : Fin (k+1) → Fin a) (δ : Fin a)
    (hfin : ∀ t : Fin (k+1) → RV (M := M),
      {r : Fin a → RV (M := M) | (Fin.elim0,r) ∈ carrier U ∧ r ∘ ι = t}.Finite)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) :
    VolumeObjectGamma (nativeCoordinateDensityVolumeObject hc C U ι δ hfin hδ) G := by
  have hD : GammaSetDefinable G {p : Point (M := M) 0 a |
      p.2 ∈ (rawVolumeContractionLabels hc U).carrier} := by
    have he : carrier U = {p : Point (M := M) 0 a | p.2 ∈ (rawVolumeContractionLabels hc U).carrier} := by
      ext p
      have hp : p = (Fin.elim0,p.2) := Prod.ext (funext (fun i => Fin.elim0 i)) rfl
      change p ∈ carrier U ↔ p.2 ∈ (rawVolumeContractionLabels hc U).carrier
      rw [mem_rawVolumeContractionLabels hc U p.2,← hp]
    exact he ▸ hU
  exact ⟨gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real ι) hD (fun _ => rfl),
    gamma_real_rv_map_graph hc G _ (rvCoordinateSelectMap G.real (fun _ : Fin 1 => δ)) hD (fun _ => rfl)⟩

theorem selected_standard_volume_object_gamma
    (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (Ξ : Set (Values.Gamma (M := M))) (G : Base (M := M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (ρ : Fin d → Fin a) (δ : Fin a)
    (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin d → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) :
    VolumeObjectGamma (selectedStandardVolumeObject hc C Ξ A ρ δ hδ hfin T) G :=
  native_coordinate_density_volume_object_gamma hc C G _ (gamma_program_final_set T.program hT) _ _ _ _

theorem raw_standard_volume_object_gamma (hc : CanonicalStructure.IsCanonical (M := M))
    (C : BaseContext M) (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) :
    VolumeObjectGamma (rawStandardVolumeObject hc C G.gamma A hfin δ hδ T) G :=
  gamma_coordinate_density_object_graphs hc C
    (FiniteRV.gammaRawFiniteContraction C.uncountable.le C.saturated
      ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGC hA hfin T hT)
    (Set.Subset.refl _) (suffixIndex T.program.rvArity_le δ) (raw_standard_retained_density_nonzero T δ hδ)

theorem raw_standard_volume_normalization
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M))
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) :
    CommonContextVolumeEquivalent G C
      ⟨rawStandardVolumeObject hc C G.gamma A hfin δ hδ T,
        raw_standard_volume_object_gamma hc C G hGC A hA hfin δ hδ T hT⟩
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ
        (fun p => hδ p.val p.property) T hT) := by
  obtain ⟨hZ,D,hCD,e,he⟩ := finite_contraction_normalization_volume_iso hc C C (Set.Subset.refl _)
    C.uncountable.le C.saturated ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hGC A
    hA hfin T hT δ (fun p => hδ p.val p.property)
  exact CommonContextVolumeEquivalent.of_extended_iso hCD e he

theorem retained_same_order_common_context
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (G : Base (M := M)) (hGC : G.real ⊆ (C.base : Set M)) (hΞ : Cardinal.mk G.gamma < C.κ)
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField G.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ G.gamma) (hγ1 : 1 < γ)
    (A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hA : GammaSetDefinable G (carrier A))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p ∈ carrier A, (p.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (n+1))} (T E : StandardContraction A σ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ
        (fun p => hδ p.val p.property) T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated
        ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hc C hGC A hA hfin δ
        (fun p => hδ p.val p.property) E hE) :=
  retained_density_same_order_contractions_compare (G := G) (k := n) hc C C.uncountable.le C.saturated
    ((Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small) hΞ
    γ hγ hγ1 hGC hGeneric A hA hfin δ (fun p => hδ p.val p.property) T E hT hE

end IntegrationInACVF.Section7.GammaNamed
