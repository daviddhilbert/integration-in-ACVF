module

public import Integration7.OrdinaryVolumeFamilyAEHeadGeometry
public import Integration7.VolumeFamilyFormulaWitnessDescent

@[expose] public section

/-! Ordinary AE representatives and arbitrary choices of their
first head preparation give the same positive-valued AE head function. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {C : BaseContext M} {n a b : ℕ}

theorem ordinary_family_head_integral_comparison_of_ae
    (hc : CanonicalStructure.IsCanonical (M := M))
    (Ξ : Set (Values.Gamma (M := M))) (hΞ : Cardinal.mk Ξ < C.κ)
    (hNames : commonRealNames (⟨(C.base : Set M),Ξ⟩ : Base (M := M)) ⊆ (C.base : Set M))
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ Ξ) (hγ1 : 1 < γ)
    (F : OrdinaryVFVolumeFamily C ((n+1)+1) a) (G : OrdinaryVFVolumeFamily C ((n+1)+1) b)
    (hAE : AEOrdinaryRVVolumeFunctionEquivalent hc C ⟨a,F⟩ ⟨b,G⟩)
    (T : HeadPreparation (nativeMixedVolumeDomain hc F.fullVFObject.densityGraph.domain))
    (E : HeadPreparation (nativeMixedVolumeDomain hc G.fullVFObject.densityGraph.domain)) :
    AERVVolumeFunctionEquivalent hc C ⟨1+T.arity,F.headIntegral hc Ξ T⟩
      ⟨1+E.arity,G.headIntegral hc Ξ E⟩ := by
  let B : Base (M := M) := ⟨(C.base : Set M),Ξ⟩
  have hTarget := (gammaLogicInput B).real_set _ (setDefinable T.target)
  have hETarget := (gammaLogicInput B).real_set _ (setDefinable E.target)
  let δ := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) (Fin.last a))
  let ε := Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le E.special) (Fin.last b))
  let LF := gammaSelectedVolumeSchema (k := 0) T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1))) δ
  let RG := gammaSelectedVolumeSchema (k := 0) E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (b+1))) ε
  obtain ⟨NF,hNF⟩ := selected_volume_schema_uniform_bound (k := 0) C.uncountable.le C.saturated C.small hΞ
    T.contractedSet (gamma_headImage T.target hTarget)
    (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin (a+1))) δ
    (head_retained_density_nonzero T (Fin.last a) F.densityGraph_label_nonzero)
    (F.headIntegral hc Ξ T).finite_selected
  obtain ⟨NG,hNG⟩ := selected_volume_schema_uniform_bound (k := 0) C.uncountable.le C.saturated C.small hΞ
    E.contractedSet (gamma_headImage E.target hETarget)
    (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin (b+1))) ε
    (head_retained_density_nonzero E (Fin.last b) G.densityGraph_label_nonzero)
    (G.headIntegral hc Ξ E).finite_selected
  apply volume_family_ae_of_generic_formula_witnesses hc Ξ hΞ hNames
    (F.headIntegral hc Ξ T) (G.headIntegral hc Ξ E) (LF.withBound NF) (RG.withBound NG)
  · intro x
    exact (native_coordinate_volume_family_schema_row hc T.contractedSet _ _ _ δ _ x).congr
      (GammaRVVolumeSchema.sameRow_symm (LF.withBound_sameRow NF _ (fun j => (x j).property)))
  · intro x
    exact (native_coordinate_volume_family_schema_row hc E.contractedSet _ _ _ ε _ x).congr
      (GammaRVVolumeSchema.sameRow_symm (RG.withBound_sameRow NG _ (fun j => (x j).property)))
  · intro x hx
    apply gamma_volume_formula_witness_from_geometry hc C.uncountable.le C.saturated C.model00
      C.small hΞ _ _ _ (hNF x) (hNG x)
    apply GammaRVVolumeSchema.commonByGammaGeometry_transport_rows
      (F := LF) (G := RG) (F' := LF.withBound NF) (G' := RG.withBound NG)
      (z := fun j => (x j).val) (t := fun j => (x j).val) rfl
      (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
    exact ordinary_family_head_geometry_of_ae hc Ξ hΞ γ hγ hγ1 F G hAE T E x hx

end IntegrationInACVF.Section7
