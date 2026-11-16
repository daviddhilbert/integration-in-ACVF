module

public import Integration7.NativeRVGraphVolumeRefinements
public import Integration7.OriginalBaseFiniteRelativeContractions
public import Integration7.DensityGraphVolumeBijections
public import Integration7.NativeVolumeMapRealization
public import Integration7.CommonContextVolumeEquivalences
public import Integration7.VFStandardVolumeContractionObjects
public import Integration7.RetainedDensityContractionObjects

@[expose] public section

/-! A literal retained density and the actual density-graph presentation
give the same contraction volume class. The graph map is a genuine
VF volume bijection preserving every VF coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n a : ℕ}

theorem retained_density_graph_contraction_comparison
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (A : DefSet (M := M) (C.base : Set M) (n+1) a)
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (ω : VolumeForm (rawSpecialSet hc A)) (δ : Fin a) (hω : ∀ p, ω.value p = p.val.2 δ)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction A σ) :
    let G : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
    let U := nativeMixedVFVolumeObject hc A hfin ω
    let hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero := fun p =>
      (rv_nonzero_iff_raw _).mp (fun hz => ω.nonzero ⟨p.val,p.property⟩ ((hω ⟨p.val,p.property⟩).trans hz))
    ∀ E : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) σ,
    CommonContextVolumeEquivalent G C
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated C.small hc C
        (Set.Subset.refl _) A ((gammaLogicInput G).real_set _ (setDefinable A)) hfin δ hδ T
        (gamma_program_over_real_base G T.program))
      ⟨U.standardContractionObject hc C Ξ E,U.standardContractionObject_gamma hc C Ξ E⟩ := by
  intro G U hδ E
  let B := nativeMixedVolumeDomain hc U.densityGraph.domain
  let e := volumeDensityGraphBijection hc C U
  let g : Map A B := nativeMixedVolumeMap hc e.map
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc e.map e.bijective
  have hA : GammaSetDefinable G (carrier A) := (gammaLogicInput G).real_set _ (setDefinable A)
  have hB : GammaSetDefinable G (carrier B) := (gammaLogicInput G).real_set _ (setDefinable B)
  have hm : PreservesVFVolume ω U.densityGraph.form (rawSpecialMap hc g) := e.preserves
  have hi : UnaryRelative g (σ 0) := fun _ _ _ => rfl
  exact finite_relative_volume_comparison_of_generic_extension (B := G) hc C C.uncountable.le
    C.saturated C.small (Set.Subset.refl _) hΞ γ hγ hγ1 (fun _ h => h)
    A B hA hB hfin U.densityGraph.finite_labels g hg ((gammaLogicInput G).real_map_graph g)
    ω U.densityGraph.form hm hi T E (gamma_program_over_real_base G T.program)
    (gamma_program_over_real_base G E.program) δ (Fin.last U.arity) hω (densityGraph_form_last U)

end IntegrationInACVF.Section7
