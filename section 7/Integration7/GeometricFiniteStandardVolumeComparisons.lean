module

public import Integration7.FiniteRawContractionVolumeRows
public import Integration7.GeometricVolumeCommonOnObjects
public import Integration7.GammaVolumeBaseEquality

@[expose] public section

/-! Recover the specified normalized finite contraction objects from a
geometric comparison of their actual complete raw coordinate/density rows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}

set_option maxHeartbeats 3200000 in
theorem finite_standard_volume_comparison_of_geometric_rows {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (k+1) a) (V : DefSet (M := M) (C.base : Set M) (k+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (k+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    {σ τ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (E : StandardContraction V τ)
    (hT : GammaProgramDefinable B T.program) (hE : GammaProgramDefinable B E.program)
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    (hGeom : (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
        T.volumeIndex (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema E.target (gamma_program_final_set E.program hE)
        E.volumeIndex (suffixIndex E.program.rvArity_le ε))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val)) :
    let R := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hU hfinU T hT
    let S := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hV hfinV E hE
    ∃ (D : BaseContext M) (hCD : (C.base : Set M) ⊆ (D.base : Set M)),
      GammaVolumeBlowupEquivalent B (D.base : Set M) k
        ⟨(gammaCoordinateDensityObject (e := k) (k := 0) hc C R (Set.Subset.refl _)
          (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)).extend hCD,
          (gamma_coordinate_density_object_graphs hc C R (Set.Subset.refl _) _ _).extend hCD⟩
        ⟨(gammaCoordinateDensityObject (e := k) (k := 0) hc C S (Set.Subset.refl _)
          (FiniteRV.contractionOldLabelIndex E ε) (normalized_contraction_retained_density_nonzero E ε hε)).extend hCD,
          (gamma_coordinate_density_object_graphs hc C S (Set.Subset.refl _) _ _).extend hCD⟩ := by
  intro R S
  obtain ⟨hZT,D₁,hCD₁,eT,heT⟩ := finite_contraction_normalization_volume_iso
    hc C C (Set.Subset.refl _) hκ hs hreal hBC U hU hfinU T hT δ hδ
  obtain ⟨hZE,D₂,hD₁D₂,eE,heE⟩ := finite_contraction_normalization_volume_iso
    hc C D₁ hCD₁ hκ hs hreal hBC V hV hfinV E hE ε hε
  let RT := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hU hfinU T hT
  let RE := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hV hfinV E hE
  let A := gammaCoordinateDensityObject (e := k) (k := 0) hc C RT (Set.Subset.refl _)
    (suffixIndex T.program.rvArity_le δ) hZT
  let Z := gammaCoordinateDensityObject (e := k) (k := 0) hc C RE (Set.Subset.refl _)
    (suffixIndex E.program.rvArity_le ε) hZE
  let z : Fin 0 → M := fun j => (Fin.elim0 j : VF (M := M)).val
  have hEmpty : (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = B := by
    change (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = ⟨B.real,B.gamma⟩
    rw [Set.range_eq_empty,Set.union_empty]
  have hA : VolumeObjectGamma A B := gamma_coordinate_density_object_graphs hc C RT (Set.Subset.refl _) _ _
  have hZ : VolumeObjectGamma Z B := gamma_coordinate_density_object_graphs hc C RE (Set.Subset.refl _) _ _
  obtain ⟨D₃,hCD₃,hRaw⟩ := GammaRVVolumeSchema.commonByGammaGeometry_on_objects hc C A Z _ _ z
    (finite_raw_contraction_volume_schema_row hc C hκ hs hreal hBC U hU hfinU T hT δ hZT)
    (finite_raw_contraction_volume_schema_row hc C hκ hs hreal hBC V hV hfinV E hE ε hZE)
    (hEmpty.symm ▸ hA) (hEmpty.symm ▸ hZ)
    (by rintro q (hq | ⟨i,_⟩); exact hBC hq; exact Fin.elim0 i) hGeom
  obtain ⟨D,hD₂D,hD₃D⟩ := volume_context_join_exists D₂ D₃
  let hCD := hCD₁.trans (hD₁D₂.trans hD₂D)
  have hMiddle := (hRaw.rebase hEmpty).extend hD₃D
  refine ⟨D,hCD,GammaVolumeBlowupEquivalent.trans hc D B ?_ (hMiddle.trans hc D B ?_)⟩
  · exact GammaVolumeBlowupEquivalent.of_iso D B
      ((eT.extend (hD₁D₂.trans hD₂D)).symm hc D)
      ((heT.extend (hD₁D₂.trans hD₂D)).symm hc D B)
  · exact GammaVolumeBlowupEquivalent.of_iso D B (eE.extend hD₂D) (heE.extend hD₂D)

end IntegrationInACVF.Section7
