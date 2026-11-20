import Integration7.GammaFunHeadIntegrals

/-! **Almost-everywhere equivalence from rows at generic points.** Two Gamma-named presentations
whose rows are Gamma-equivalent at every VF point algebraically independent over the Gamma-named
base are almost-everywhere equivalent: the density-graph schemata give definable witness loci. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section9
open SpecialTransformations.Section4 (vfValues)
open SpecialTransformations.Section5 (Point GammaSetDefinable GammaGraphDefinable gammaLogicInput carrier VF RV pointMapGraph headImage)
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7.GammaFun
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n k : ℕ}
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)

set_option quotPrecheck false
local notation "𝔅" => gammaNamedBase C Ξ
local notation "𝔇" => gammaNamedCodeContext C Ξ hΞ
local notation "𝔖" => ((gammaNamedCodeContext C Ξ hΞ).base : Set M)

set_option maxHeartbeats 1600000 in
/-- **Generic rows determine almost-everywhere classes.** -/
theorem presentation_ae_of_generic_rows (F H : Presentation C Ξ hΞ n k)
    (h : ∀ x, AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x →
      GammaRowsEquivalent hc 𝔇 𝔅 F.gamma H.gamma x) :
    AEEquivalent hc C Ξ hΞ F H := by
  classical
  have hreal := small_gamma_named_real C Ξ hΞ
  have hUF := F.gamma.native_domain hc
  have hUH := H.gamma.native_domain hc
  let L0 := gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc F.family.densityGraph.domain) hUF
    F.family.densityGraph.selected (Fin.last F.arity)
  let R0 := gammaSelectedVolumeSchema (nativeMixedVolumeDomain hc H.family.densityGraph.domain) hUH
    H.family.densityGraph.selected (Fin.last H.arity)
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    (nativeMixedVolumeDomain hc F.family.densityGraph.domain) hUF F.family.densityGraph.selected (Fin.last F.arity)
    (fun q hq => F.family.densityGraph_label_nonzero q hq) F.family.densityGraph.finite_selected
  obtain ⟨NH,hNH⟩ := selected_volume_schema_uniform_bound (𝔇).uncountable.le (𝔇).saturated hreal hΞ
    (nativeMixedVolumeDomain hc H.family.densityGraph.domain) hUH H.family.densityGraph.selected (Fin.last H.arity)
    (fun q hq => H.family.densityGraph_label_nonzero q hq) H.family.densityGraph.finite_selected
  let L := L0.withBound NF
  let R := R0.withBound NH
  have PL : ∀ x, RVVolumeSchemaRow (F.family.densityGraph.rowInContext x) L (vfValues x) := fun x =>
    (F.family.densityGraph_schema_rows_of hc hUF x).congr
      (GammaRVVolumeSchema.sameRow_symm (L0.withBound_sameRow NF _ (fun j => (x j).property)))
  have PR : ∀ x, RVVolumeSchemaRow (H.family.densityGraph.rowInContext x) R (vfValues x) := fun x =>
    (H.family.densityGraph_schema_rows_of hc hUH x).congr
      (GammaRVVolumeSchema.sameRow_symm (R0.withBound_sameRow NH _ (fun j => (x j).property)))
  have hWitness : ∀ x, AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x →
      ∃ W : GammaVolumeCommonSchema L R, W.valid (vfValues x) := by
    intro x hx
    apply gamma_volume_formula_witness_from_geometry hc (𝔇).uncountable.le (𝔇).saturated (𝔇).model00
      hreal hΞ _ _ _ (hNF x) (hNH x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := L0) (G := R0) (F' := L) (G' := R)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact gamma_rows_schema_common hc 𝔇 𝔅 F.gamma H.gamma x (h x hx)
  obtain ⟨J,hJ⟩ := gamma_finite_witnesses_at_generic_points 𝔅 (𝔇).uncountable.le (𝔇).saturated
    (small_gamma_named_real C Ξ hΞ) hΞ
    (fun W : GammaVolumeCommonSchema L R => {z | W.valid z}) (fun W => W.valid_definable hc) hWitness
  let R1 := ⋃ W ∈ J, {z | W.valid z}
  have hR1 : DefinableOverBase 𝔅 (fun _ => .vf) R1 :=
    DefinableOverBase.finite_iUnion J (fun W : GammaVolumeCommonSchema L R => {z | W.valid z})
      (fun W _ => W.valid_definable hc)
  let Good := pureVFFormulaLocus R1 (hR1.common_names.mono (gamma_named_code_context_names C Ξ hΞ))
  let Eset := (SpecialTransformations.DefinableGeometry.DefSet.univ
    (SpecialTransformations.Section4.rawVFSpace (M := M) (n+1)) 𝔖).sdiff Good
  have hAll : GammaSetDefinable 𝔅 (Set.univ : Set (Point (M := M) (n+1) 0)) :=
    (gammaLogicInput 𝔅).real_set _
      (SpecialTransformations.Section5.setDefinable
        (SpecialTransformations.Section5.PresentedSet.univ (SpecialTransformations.Section5.pointSpace (M := M) (n+1) 0)
          (gammaNamedBase C Ξ).real))
  let E : GammaVFSet C Ξ hΞ n := ⟨Eset,by
    have h := (gammaLogicInput 𝔅).sdiff hAll (HK.gamma_pure_vf_locus hR1)
    convert h using 1
    ext q
    exact ⟨fun hq => ⟨Set.mem_univ _,hq.2⟩,fun hq => ⟨Set.mem_univ _,hq.2⟩⟩⟩
  have hGood : ∀ x, AlgebraicIndependent (vfParameterField (gammaNamedBase C Ξ).real) x → x ∈ Good.carrier := by
    intro x hx
    obtain ⟨W,hWJ,hW⟩ := hJ x hx
    exact Set.mem_iUnion.mpr ⟨W,Set.mem_iUnion.mpr ⟨hWJ,hW⟩⟩
  refine ⟨E,pure_vf_dimension_lt_of_no_independent hc 𝔇 (Nat.zero_lt_succ _) Eset ?_,?_⟩
  · intro p hp
    exact p.property.2 (hGood p.val
      (algebraicIndependent_of_larger_base (gamma_named_code_context_base C Ξ hΞ) _ hp))
  · intro x hx
    have hg : x ∈ Good.carrier := by
      by_contra h
      exact hx ⟨Set.mem_univ _,h⟩
    change vfValues x ∈ R1 at hg
    obtain ⟨W,hW⟩ := Set.mem_iUnion.mp hg
    obtain ⟨_,hW⟩ := Set.mem_iUnion.mp hW
    let Cx := vfParameterVolumeContext 𝔇 x
    apply (gammaVolumeBlowupClass_eq_iff hc Cx _).mpr
    have hW' : W.valid (vfValues x) := hW
    obtain ⟨D,hDE,hCommon⟩ := GammaVolumeCommonSchema.realizeOnGamma hc Cx W (vfValues x) hW' (PL x) (PR x)
      (F.gamma.densityGraph_row hc x) (H.gamma.densityGraph_row hc x)
      ((gamma_named_code_context_base C Ξ hΞ).trans (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inl hy)))
      (fun y hy => vfParameterVolumeContext_contains 𝔇 x (Or.inr hy))
    have h1 := GammaVolumeBlowupEquivalent.of_iso D (rowGammaBase 𝔅 x)
      (U := ⟨(F.family.rowInContext x).extend hDE,(F.gamma.row hc x).extend hDE⟩)
      (V := ⟨(F.family.densityGraph.rowInContext x).extend hDE,(F.gamma.densityGraph_row hc x).extend hDE⟩)
      ((F.family.densityGraphRowIso hc x).extend hDE) ((F.gamma.densityGraphRowIso hc x).extend hDE)
    have h2 := GammaVolumeBlowupEquivalent.of_iso D (rowGammaBase 𝔅 x)
      (U := ⟨(H.family.densityGraph.rowInContext x).extend hDE,(H.gamma.densityGraph_row hc x).extend hDE⟩)
      (V := ⟨(H.family.rowInContext x).extend hDE,(H.gamma.row hc x).extend hDE⟩)
      (((H.family.densityGraphRowIso hc x).symm hc Cx).extend hDE)
      (((H.gamma.densityGraphRowIso hc x).symm hc Cx _).extend hDE)
    exact (show CommonContextVolumeEquivalent (rowGammaBase 𝔅 x) Cx ⟨_,F.gamma.row hc x⟩ ⟨_,H.gamma.row hc x⟩
      from ⟨D,hDE,(h1.trans hc D _ hCommon).trans hc D _ h2⟩).descend hc Cx
        (row_context_names 𝔇 𝔅 (gamma_named_code_context_names C Ξ hΞ) x)

end IntegrationInACVF.Section7.GammaFun
