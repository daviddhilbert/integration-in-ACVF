module

public import Integration7.GammaRVGraphRefinementGeometry
public import Integration7.RetainedDensityContractionObjects
public import Integration7.MixedRetainedLabelVolumeForms
public import Integration7.OriginalBaseRelativeVolumeComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Any two specified same-order contractions before and after an RV
graph refinement have common forward Gamma volume blowups. The density
is the same literal retained label, without a constancy hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5 SpecialTransformations.Section9
open IntegrationInACVF.Section4 IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {k a d : ℕ}

theorem rv_graph_refinement_density_nonzero (A : DefSet (M := M) S (k+1) a)
    (P : GammaRVMap B (carrier A) d) (hNames : commonRealNames B ⊆ S)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero) :
    ∀ q : gammaRVGraphRefinement A P hNames, (q.val.2 (Fin.castAdd d δ)).val ≠ iRVZero := by
  rintro ⟨q,p,rfl⟩
  change (Fin.append p.val.2 (P.toFun p) (Fin.castAdd d δ)).val ≠ iRVZero
  rw [Fin.append_left]
  exact hδ p

set_option maxHeartbeats 1600000 in
theorem rv_graph_refinement_contraction_common_blowup {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hNames : commonRealNames B ⊆ (C.base : Set M))
    (hGeneric : ∀ {p : ℕ} (x : Fin p → VF (M := M)), AlgebraicIndependent (vfParameterField B.real) x →
      AlgebraicIndependent (vfParameterField (C.base : Set M)) x)
    (A : DefSet (M := M) (C.base : Set M) (k+1) a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (P : GammaRVMap B (carrier A) d) (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (k+1))}
    (T : StandardContraction A σ) (E : StandardContraction (gammaRVGraphRefinement A P hNames) σ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program) :
    let H := gammaRVGraphRefinement A P hNames
    let hH := gamma_rv_graph_refinement_target_gamma A P hNames
    let hfinH := gamma_rv_graph_refinement_finite_labels A hfin P hNames
    let hε := rv_graph_refinement_density_nonzero A P hNames δ hδ
    let U := retainedDensityContractionGammaObject hκ hs hreal hc C hBC A hA hfin δ hδ T hT
    let V := retainedDensityContractionGammaObject hκ hs hreal hc C hBC H hH hfinH (Fin.castAdd d δ) hε E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) k (U.extend hCD) (V.extend hCD) := by
  intro H hH hfinH hε U V
  let f := Map.toImage (gammaRVGraphRefinementMap A P hNames)
  let ω := mixedRetainedLabelVolumeForm (rawSpecialSet hc A) δ (fun p => hδ ⟨p.val,p.property⟩)
  let π := mixedRetainedLabelVolumeForm (rawSpecialSet hc H) (Fin.castAdd d δ) (fun q => hε ⟨q.val,q.property⟩)
  have hJ := vfJacobianOne_of_preservesVF hc C (Nat.zero_lt_succ k) (rawSpecialMap hc f) (fun _ => rfl)
  have hm : PreservesVFVolume ω π (rawSpecialMap hc f) := hJ.mono (fun p hp =>
    ⟨1,hp,by rw [RVOperations.rv_one,mul_one];exact (Fin.append_left p.val.2 (P.toFun ⟨p.val,p.property⟩) δ).symm⟩)
  have hGeom := standard_relative_volume_schema_comparison_of_generic_extension hc C hκ hs hreal hgamma γ hγ hγ1
    hBC hGeneric A H hA hH hfin hfinH f (gamma_rv_graph_refinement_bijective A P hNames)
    (gamma_rv_graph_refinement_map_gamma A P hNames) ω π δ (Fin.castAdd d δ) (fun _ => rfl) (fun _ => rfl) hm
    (gamma_rv_graph_refinement_unary_relative A P hNames (σ 0)) T E hT hE
  exact finite_standard_volume_comparison_of_geometric_rows hc C hκ hs hreal hBC A H hA hH hfin hfinH
    T E hT hE δ (Fin.castAdd d δ) hδ hε hGeom

end IntegrationInACVF.Section7
