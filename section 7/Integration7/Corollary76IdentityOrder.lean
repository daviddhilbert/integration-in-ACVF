module

public import Integration7.OrderedRelativeVolumeSchemaComparison
public import Integration7.GeometricFiniteStandardVolumeComparisons
public import Integration7.DensityGraphRelativeBijections
public import IntegrationSection6.StandardProgramPresentations
public import Integration7.UnaryContractionGammaVolumeComparison
public import Integration7.VFStandardVolumeContractionObjects
public import Integration7.NativeVolumeMapRealization
public import Integration7.DensityGraphVolumeBijections

@[expose] public section

/-! Corollary 7.6 in every positive VF dimension for a map relatively
unary in the first coordinate and specified identity-order contractions.
Only global almost-everywhere measure preservation is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section5 (gammaLogicInput setDefinable pointMapGraph GammaGraphDefinable GammaSetDefinable carrier)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

set_option maxHeartbeats 3200000 in
theorem corollary_7_6_identity_order {k : ℕ}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (U V : PositiveVFVolumeObject (M := M) (C.base : Set M) k) (f : VFVolumeBijection U V)
    (hi : ∀ p : U.domain, ∀ j, j ≠ 0 → (f.map p).val.1 j = p.val.1 j)
    (T : StandardContraction (nativeMixedVolumeDomain hc U.densityGraph.domain) (Equiv.refl _))
    (E : StandardContraction (nativeMixedVolumeDomain hc V.densityGraph.domain) (Equiv.refl _)) :
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (D.base : Set M) k
        ⟨(U.standardContractionObject hc C Ξ T).extend hCD,
          (U.standardContractionObject_gamma hc C Ξ T).extend hCD⟩
        ⟨(V.standardContractionObject hc C Ξ E).extend hCD,
          (V.standardContractionObject_gamma hc C Ξ E).extend hCD⟩ := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  let A := nativeMixedVolumeDomain hc U.densityGraph.domain
  let Z := nativeMixedVolumeDomain hc V.densityGraph.domain
  let fD := f.onDensityGraphs hc C
  let g := nativeMixedVolumeMap hc fD.map
  have hg : Function.Bijective g := native_mixed_volume_map_bijective hc fD.map fD.bijective
  have hgΓ : GammaGraphDefinable B (pointMapGraph g) := (gammaLogicInput B).real_map_graph g
  have hA : GammaSetDefinable B (carrier A) := (gammaLogicInput B).real_set _ (setDefinable A)
  have hZ : GammaSetDefinable B (carrier Z) := (gammaLogicInput B).real_set _ (setDefinable Z)
  have hm : PreservesVFVolume U.densityGraph.form V.densityGraph.form (rawSpecialMap hc g) := fD.preserves
  have hT := gamma_program_over_real_base B T.program
  have hE := gamma_program_over_real_base B E.program
  let P := orderedCastSource T.program (vfPermutationImage_id_eq A)
  let Q := orderedCastSource E.program (vfPermutationImage_id_eq Z)
  have hP := gamma_orderedCastSource T.program (vfPermutationImage_id_eq A) hT
  have hQ := gamma_orderedCastSource E.program (vfPermutationImage_id_eq Z) hE
  have hPvol : P.volumeIndex = T.volumeIndex := by
    rw [show P.volumeIndex = T.program.volumeIndex from orderedCastSource_volumeIndex _ _]
    rfl
  have hQvol : Q.volumeIndex = E.volumeIndex := by
    rw [show Q.volumeIndex = E.program.volumeIndex from orderedCastSource_volumeIndex _ _]
    rfl
  have hGeom := ordered_relative_volume_schema_comparison hc C C.uncountable.le
    C.saturated C.small hΞ γ hγ hγ1 (Set.Subset.refl _) rfl
    A Z hA hZ U.densityGraph.finite_labels V.densityGraph.finite_labels
    g hg hgΓ (f.onDensityGraphs_relative hc C 0 hi)
    U.densityGraph.form V.densityGraph.form (Fin.last U.arity) (Fin.last V.arity)
    (densityGraph_form_last U) (densityGraph_form_last V) hm P Q hP hQ
  have hGeom' : (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
      T.volumeIndex (suffixIndex T.program.rvArity_le (Fin.last U.arity))).commonByGammaGeometry
    (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE)
      E.volumeIndex (suffixIndex E.program.rvArity_le (Fin.last V.arity)))
    (fun j : Fin 0 => (Fin.elim0 j : SpecialTransformations.Section5.VF (M := M)).val) := by
    simpa only [hPvol,hQvol] using hGeom
  exact finite_standard_volume_comparison_of_geometric_rows hc C C.uncountable.le C.saturated C.small
    (Set.Subset.refl _) A Z hA hZ U.densityGraph.finite_labels V.densityGraph.finite_labels
    T E hT hE (Fin.last U.arity) (Fin.last V.arity)
    (fun q => (rv_nonzero_iff_raw _).mp (fun h => U.densityGraph.form.nonzero q ((densityGraph_form_last U q).trans h)))
    (fun q => (rv_nonzero_iff_raw _).mp (fun h => V.densityGraph.form.nonzero q ((densityGraph_form_last V q).trans h))) hGeom'

end IntegrationInACVF.Section7
