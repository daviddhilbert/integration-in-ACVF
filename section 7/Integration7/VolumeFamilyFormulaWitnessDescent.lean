import Integration7.NativeCoordinateVolumeFamilyRows
import Integration7.GammaVolumeCommonRowRealization
import Integration7.GenericGammaWitnessCovers
import Integration7.PureVFFormulaLoci

/-! Generic formula witnesses give equality of the actual functions
outside one original-base definable VF-small set. A finite witness cover
and original-Gamma realization keep the descent independent of internal
presentation contexts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b k : ℕ}

theorem volume_family_formula_witness_row_descend
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M)))
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C n a k) (G : SelectedVFVolumeFamily C n b k)
    (L : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n a k (fun _ => .vf))
    (R : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) n b k (fun _ => .vf))
    (x : Fin n → VFType (M := M))
    (PL : RVVolumeSchemaRow (F.rowInContext x) L (vfValues x))
    (PR : RVVolumeSchemaRow (G.rowInContext x) R (vfValues x))
    (H : GammaVolumeCommonSchema L R) (hH : H.valid (vfValues x)) :
    VolumeBlowupEquivalent (F.rowInContext x) (G.rowInContext x) := by
  let D := vfParameterVolumeContext C x
  let Bx : Base (M := M) := ⟨(C.base : Set M) ∪ Set.range (fun j => (x j).val),Ξ⟩
  let hF := F.rowInContext_gamma hc Ξ x
  let hG := G.rowInContext_gamma hc Ξ x
  obtain ⟨E,hDE,hCommon⟩ := H.realizeOnGamma hc D (vfValues x) hH PL PR hF hG
    (Set.subset_union_left.trans (vfParameterVolumeContext_contains C x))
    (Set.subset_union_right.trans (vfParameterVolumeContext_contains C x))
  have hContext : CommonContextVolumeEquivalent Bx D
      ⟨F.rowInContext x,hF⟩ ⟨G.rowInContext x,hG⟩ := ⟨E,hDE,hCommon⟩
  exact (hContext.descend hc D (vf_parameter_volume_context_contains_common_names Ξ hNames x)).toOrdinary hc D Bx

theorem volume_family_ae_of_generic_formula_witnesses
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (F : SelectedVFVolumeFamily C (n+1) a k) (G : SelectedVFVolumeFamily C (n+1) b k)
    (L : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (n+1) a k (fun _ => .vf))
    (R : GammaRVVolumeSchema (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) (n+1) b k (fun _ => .vf))
    (PL : ∀ x, RVVolumeSchemaRow (F.rowInContext x) L (vfValues x))
    (PR : ∀ x, RVVolumeSchemaRow (G.rowInContext x) R (vfValues x))
    (hWitness : ∀ x, AlgebraicIndependent (vfParameterField (C.base : Set M)) x →
      ∃ H : GammaVolumeCommonSchema L R, H.valid (vfValues x)) :
    AERVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩ := by
  classical
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points B C.uncountable.le C.saturated C.small hΞ
    (fun H : GammaVolumeCommonSchema L R => {z | H.valid z}) (fun H => H.valid_definable hc) hWitness
  let Good := pureVFFormulaLocus (⋃ H ∈ J, {z | H.valid z})
    (((DefinableOverBase.finite_iUnion J (fun H : GammaVolumeCommonSchema L R => {z | H.valid z})
      (fun H _ => H.valid_definable hc)).common_names).mono hNames)
  let E := (DefSet.univ (rawVFSpace (M := M) (n+1)) (C.base : Set M)).sdiff Good
  have hGood : ∀ x, AlgebraicIndependent (vfParameterField (C.base : Set M)) x → x ∈ Good.carrier := by
    intro x hx
    obtain ⟨H,hHJ,hH⟩ := hJ x hx
    exact Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hHJ,hH⟩⟩
  refine ⟨E,pure_vf_dimension_lt_of_no_independent hc C (Nat.zero_lt_succ _) E ?_,?_⟩
  · intro p hp
    exact p.property.2 (hGood p.val hp)
  · intro x hx
    have hg : x ∈ Good.carrier := by
      by_contra h
      exact hx ⟨Set.mem_univ _,h⟩
    change vfValues x ∈ ⋃ H ∈ J, {z | H.valid z} at hg
    obtain ⟨H,hH⟩ := Set.mem_iUnion.mp hg
    obtain ⟨hHJ,hH⟩ := Set.mem_iUnion.mp hH
    exact (positiveVolumeBlowupClass_eq_iff hc (vfParameterVolumeContext C x)).mpr
      (volume_family_formula_witness_row_descend hc Ξ hNames F G L R x (PL x) (PR x) H hH)

end IntegrationInACVF.Section7
