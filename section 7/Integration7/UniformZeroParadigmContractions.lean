module

public import Integration7.UniformCellRVParadigmPartitions
public import Integration7.UniformZeroParadigmDimension
public import Integration7.RetainedDensitySmallDimensionContractions

@[expose] public section

/-! The actual zero-paradigm part of the entire cell family has VF
dimension at most one. All specified contraction orders therefore have
empty essential volume objects and compare over the original Gamma base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section4 IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.UniformMixedCellPresentation
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Base (M := M)} {S : Set M} {m : ℕ}
variable {A : DefSet (M := M) S 2 m}

def zeroNativePart (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    DefSet (M := M) S 2 (m+F.arity) :=
  PresentedSet.mk (F.zeroParadigmPart hNames) (SetDefinable.mono _
    (gamma_native_set_common_names (F.zero_paradigm_part_gamma hNames)) hNames)

theorem zero_native_part_gamma (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S) : GammaSetDefinable G (carrier (F.zeroNativePart hNames)) :=
  F.zero_paradigm_part_gamma hNames

theorem zero_native_part_finite_labels (F : UniformMixedCellPresentation G (carrier A))
    (hNames : commonRealNames G ⊆ S)
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite) :
    ∀ x : Fin 2 → VF (M := M),
      {r : Fin (m+F.arity) → RV (M := M) | (x,r) ∈ carrier (F.zeroNativePart hNames)}.Finite := by
  intro x
  exact (gamma_rv_graph_refinement_finite_labels A hfin F.parameters hNames x).subset (fun r hr => hr.1)

set_option maxHeartbeats 1000000 in
theorem zero_native_part_dimension (hc : CanonicalStructure.IsCanonical (M := M))
    (F : UniformMixedCellPresentation G (carrier A)) (hNames : commonRealNames G ⊆ S) :
    vfDim (SpecialTransformations.Section4.rawRVSpace (M := M) 1) (rawSpecialSet hc (F.zeroNativePart hNames)) ≤ 1 := by
  apply mixed_vf_dimension_le_one_of_coordinate hc _ 1
  intro p q hVF hRV
  let pH : gammaRVGraphRefinement A F.parameters hNames := ⟨p.val,p.property.1⟩
  let qH : gammaRVGraphRefinement A F.parameters hNames := ⟨q.val,q.property.1⟩
  have htP := (F.mem_zero_paradigm_rv_labels hNames pH).mp p.property.2
  have htQ := (F.mem_zero_paradigm_rv_labels hNames qH).mp q.property.2
  have he : erase 0 pH.val = erase 0 qH.val := by
    apply Prod.ext
    · funext i
      fin_cases i
      · rfl
      · exact hVF
    · exact hRV
  have hCentre := F.refinement_centre_constant hNames pH qH he
  have hHead := (F.zero_paradigm_head_value hNames pH htP).trans
    (hCentre.trans (F.zero_paradigm_head_value hNames qH htQ).symm)
  funext i
  fin_cases i
  · exact hHead
  · exact hVF

theorem zero_native_part_contractions_compare
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hGC : G.real ⊆ (C.base : Set M)) (hNames : commonRealNames G ⊆ (C.base : Set M))
    {A : DefSet (M := M) (C.base : Set M) 2 m} (F : UniformMixedCellPresentation G (carrier A))
    (hfin : ∀ x : Fin 2 → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin (m+F.arity)) (hδ : ∀ p : F.zeroNativePart hNames, (p.val.2 δ).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin 2)} (T : StandardContraction (F.zeroNativePart hNames) σ)
    (E : StandardContraction (F.zeroNativePart hNames) τ)
    (hT : GammaProgramDefinable G T.program) (hE : GammaProgramDefinable G E.program) :
    let hreal : Cardinal.mk G.real < C.κ := (Cardinal.mk_le_mk_of_subset hGC).trans_lt C.small
    let Z := F.zeroNativePart hNames
    let hZ := F.zero_native_part_gamma hNames
    let hfinZ := F.zero_native_part_finite_labels hNames hfin
    GammaVolumeBlowupEquivalent G (C.base : Set M) 1
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ T hT)
      (retainedDensityContractionGammaObject C.uncountable.le C.saturated hreal hc C hGC Z hZ hfinZ δ hδ E hE) := by
  intro hreal Z hZ hfinZ
  exact small_dimension_retained_density_contractions_compare C.uncountable.le C.saturated hreal
    hc C hGC Z hZ hfinZ δ hδ T hT ((F.zero_native_part_dimension hc hNames).trans_lt (by decide)) E hE

end IntegrationInACVF.Section7.UniformMixedCellPresentation
