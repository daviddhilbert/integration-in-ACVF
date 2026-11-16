module

public import IntegrationSection6.FiniteSelectedContractionSlices
public import Integration7.GammaCoordinateDensityEquivalences
public import Integration7.ContractionRetainedDensityLabels
public import IntegrationSection6.RawSelectedContractions
public import IntegrationSection6.GammaSwappedVolumes

@[expose] public section

/-! First-volume normalization of a unary contraction preserves the
actual selected volume tuple and retained density, with its Gamma graph. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a k : ℕ}

set_option maxHeartbeats 1600000 in
theorem unary_selected_normalization_volume_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) 1 a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin 1 → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) :
    let Z := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs hreal hBC hU ρ hfin T hT)
    let R := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT
    ∃ hZ : ∀ u : rvObjectDomain Z.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ D : BaseContext M, ∃ hCD : (C.base : Set M) ⊆ (D.base : Set M),
    ∃ f : RVVolumeIso
      ((gammaCoordinateDensityObject (e := k+1) (k := 0) hc C Z (Set.Subset.refl _)
        (suffixIndex T.program.rvArity_le δ) hZ).extend hCD)
      ((gammaCoordinateDensityObject (e := k+1) (k := 0) hc C R (Set.Subset.refl _)
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)).extend hCD),
      f.GammaDefinable B := by
  intro Z R
  let e := FiniteRV.gammaRawSelectedNormalizationIso hκ hs hreal hBC hU ρ hfin T hT
  have hold (u : rvObjectDomain Z.object) :
      (e.equiv u).val (FiniteRV.contractionOldLabelIndex T δ) = u.val (suffixIndex T.program.rvArity_le δ) :=
    toFirstVolume_oldLabels _ _ _ _
  have hZ : ∀ u : rvObjectDomain Z.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero := by
    intro u
    rw [← hold]
    exact normalized_contraction_retained_density_nonzero T δ hδ (e.equiv u)
  have hcoord (u : rvObjectDomain Z.object) :
      gammaVolumeValue R.toGammaRVObject (e.equiv u) = gammaVolumeValue Z.toGammaRVObject u :=
    congrArg (fun t => t ∘ (@finAddFlip (k+1) 1))
      (FiniteRV.gammaRawSelectedNormalizationIso_volume hκ hs hreal hBC hU ρ hfin T hT u)
  let e' : GammaRVIso Z.toGammaRVObject R.toGammaRVObject :=
    FiniteRV.gammaIsoOfFiniteEquiv Z R e.equiv e.graph (fun u =>
      congrArg (fun t : Fin ((k+1)+1) → RV (M := M) => rawWeight (rvValues t)) (hcoord u).symm)
  obtain ⟨D,hCD,f,hf⟩ := gamma_coordinate_density_equivalence_realize hc C Z R (Set.Subset.refl _) (Set.Subset.refl _)
    (suffixIndex T.program.rvArity_le δ) (FiniteRV.contractionOldLabelIndex T δ) hZ
    (normalized_contraction_retained_density_nonzero T δ hδ) e' hcoord hold
  exact ⟨hZ,D,hCD,f,hf⟩

end IntegrationInACVF.Section7
