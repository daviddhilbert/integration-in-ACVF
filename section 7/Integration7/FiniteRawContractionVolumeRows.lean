module

public import Integration7.FiniteContractionNormalizationVolumeIso
public import Integration7.GammaSelectedVolumeSchemata
public import IntegrationSection6.RawContractionDomain

@[expose] public section

/-! The actual raw finite contraction volume object realizes the full
coordinate and retained-density schema of the specified final RV labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}

set_option maxHeartbeats 1600000 in
theorem finite_raw_contraction_volume_schema_row {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (k+1) a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) :
    let R := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hU hfin T hT
    ∀ hZ : ∀ u : rvObjectDomain R.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero,
      RVVolumeSchemaRow
        (gammaCoordinateDensityObject (e := k) (k := 0) hc C R (Set.Subset.refl _)
          (suffixIndex T.program.rvArity_le δ) hZ)
        (gammaSelectedVolumeSchema T.target (gamma_program_final_set T.program hT)
          T.volumeIndex (suffixIndex T.program.rvArity_le δ))
        (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  intro R hZ
  have hTarget := gamma_program_final_set T.program hT
  have hNZ : ∀ p ∈ carrier T.target, (p.2 (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero := by
    intro p hp
    have he : p = (Fin.elim0,p.2) := Prod.ext (funext fun i => Fin.elim0 i) rfl
    exact hZ ⟨p.2,(rawContractionDomain_iff T (Fin.elim0,p.2)).mpr (he ▸ hp)⟩
  constructor
  · intro r y
    have h := gammaSelectedLabelSchema_volume T.target hTarget T.volumeIndex
      (Fin.elim0 : Fin 0 → VF (M := M)) r y
    constructor
    · intro hz
      obtain ⟨hr,hy⟩ := h.mp hz
      exact ⟨⟨r,(rawContractionDomain_iff T (Fin.elim0,r)).mpr hr⟩,rfl,hy⟩
    · rintro ⟨u,hu,hy⟩
      exact h.mpr ⟨hu ▸ (rawContractionDomain_iff T (Fin.elim0,u.val)).mp u.property,
        (congrArg (fun r => r ∘ T.volumeIndex) hu).symm.trans hy⟩
  · intro r w
    have h := gammaSelectedVolumeSchema_density T.target hTarget T.volumeIndex
      (suffixIndex T.program.rvArity_le δ) hNZ (Fin.elim0 : Fin 0 → VF (M := M)) r w
    constructor
    · intro hz
      obtain ⟨hr,hw⟩ := h.mp hz
      exact ⟨⟨r,(rawContractionDomain_iff T (Fin.elim0,r)).mpr hr⟩,rfl,hw⟩
    · rintro ⟨u,hu,hw⟩
      exact h.mpr ⟨hu ▸ (rawContractionDomain_iff T (Fin.elim0,u.val)).mp u.property,
        (congrArg (fun r : Fin T.arity → RV (M := M) => fun _ : Fin 1 =>
          r (suffixIndex T.program.rvArity_le δ)) hu).symm.trans hw⟩

end IntegrationInACVF.Section7
