module

public import Integration7.FiniteRawContractionVolumeRows
public import Integration7.RetainedDensityContractionObjects
public import Integration7.CommonContextVolumeEquivalences
public import Integration7.VolumeSchemaRowExtension
public import Integration7.GammaVolumeBaseEquality

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Recover the literal raw coordinate/density rows from a comparison of
the specified normalized contraction volume objects. This reverses the
normalization bridge without discarding labels or density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b k : ℕ}

set_option maxHeartbeats 2400000 in
theorem geometric_rows_of_contraction_volume_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (k+1) a)
    (V : DefSet (M := M) (C.base : Set M) (k+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (k+1) → VF (M := M), {r : Fin b → RV (M := M) | (x,r) ∈ carrier V}.Finite)
    (δ : Fin a) (ε : Fin b)
    (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) (hε : ∀ p : V, (p.val.2 ε).val ≠ iRVZero)
    {σ τ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (W : StandardContraction V τ)
    (hT : GammaProgramDefinable B T.program) (hW : GammaProgramDefinable B W.program)
    (h : CommonContextVolumeEquivalent B C
      (retainedDensityContractionGammaObject hκ hs hreal hc C hBC U hU hfinU δ hδ T hT)
      (retainedDensityContractionGammaObject hκ hs hreal hc C hBC V hV hfinV ε hε W hW)) :
    (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
      T.volumeIndex (suffixIndex T.program.rvArity_le δ)).commonByGammaGeometry
      (gammaSelectedVolumeSchema W.target (gamma_program_final_set W.program hW)
        W.volumeIndex (suffixIndex W.program.rvArity_le ε))
      (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  obtain ⟨hZT,D₁,hCD₁,eT,heT⟩ := finite_contraction_normalization_volume_iso
    hc C C (Set.Subset.refl _) hκ hs hreal hBC U hU hfinU T hT δ hδ
  obtain ⟨hZW,D₂,hCD₂,eW,heW⟩ := finite_contraction_normalization_volume_iso
    hc C C (Set.Subset.refl _) hκ hs hreal hBC V hV hfinV W hW ε hε
  let RT := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hU hfinU T hT
  let RW := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hV hfinV W hW
  let XT := gammaCoordinateDensityObject (e := k) (k := 0) hc C RT (Set.Subset.refl _)
    (suffixIndex T.program.rvArity_le δ) hZT
  let XW := gammaCoordinateDensityObject (e := k) (k := 0) hc C RW (Set.Subset.refl _)
    (suffixIndex W.program.rvArity_le ε) hZW
  have hXT : VolumeObjectGamma XT B := gamma_coordinate_density_object_graphs hc C RT (Set.Subset.refl _) _ _
  have hXW : VolumeObjectGamma XW B := gamma_coordinate_density_object_graphs hc C RW (Set.Subset.refl _) _ _
  have hLeft : CommonContextVolumeEquivalent B C ⟨XT,hXT⟩
      (retainedDensityContractionGammaObject hκ hs hreal hc C hBC U hU hfinU δ hδ T hT) :=
    .of_extended_iso hCD₁ eT heT
  have hRight : CommonContextVolumeEquivalent B C ⟨XW,hXW⟩
      (retainedDensityContractionGammaObject hκ hs hreal hc C hBC V hV hfinV ε hε W hW) :=
    .of_extended_iso hCD₂ eW heW
  obtain ⟨D,hCD,hRaw⟩ := hLeft.trans hc (h.trans hc (hRight.symm hc))
  let z : Fin 0 → M := fun j => (Fin.elim0 j : VF (M := M)).val
  have hEmpty : (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = B := by
    change (⟨B.real ∪ Set.range z,B.gamma⟩ : Base (M := M)) = ⟨B.real,B.gamma⟩
    rw [Set.range_eq_empty,Set.union_empty]
  exact ⟨D,(GammaVolumeObjects.extend ⟨XT,hXT⟩ hCD).rebase hEmpty.symm,
    (GammaVolumeObjects.extend ⟨XW,hXW⟩ hCD).rebase hEmpty.symm,rfl,rfl,
    (finite_raw_contraction_volume_schema_row hc C hκ hs hreal hBC U hU hfinU T hT δ hZT).extend hCD,
    (finite_raw_contraction_volume_schema_row hc C hκ hs hreal hBC V hV hfinV W hW ε hZW).extend hCD,
    hRaw.rebase hEmpty.symm⟩

end IntegrationInACVF.Section7
