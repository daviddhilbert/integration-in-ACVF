module

public import Integration7.GammaCoordinateDensityEquivalences
public import Integration7.ContractionRetainedDensityLabels
public import IntegrationSection6.RawFiniteContractions

@[expose] public section

/-! Full first-volume normalization preserves the actual volume tuple
and retained density for every positive-dimensional finite contraction.
This includes a first unary contraction with no old selected coordinate. -/

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
theorem finite_contraction_normalization_volume_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (k+1) a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ p : U, (p.val.2 δ).val ≠ iRVZero) :
    let Z := FiniteRV.gammaRawFiniteContraction hκ hs hreal hBC hU hfin T hT
    let R := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hU hfin T hT
    ∃ hZ : ∀ u : rvObjectDomain Z.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ (D : BaseContext M) (hCD : (C₀.base : Set M) ⊆ (D.base : Set M)),
    ∃ f : RVVolumeIso
      ((gammaCoordinateDensityObject (e := k) (k := 0) hc C₀ Z hCC₀
        (suffixIndex T.program.rvArity_le δ) hZ).extend hCD)
      ((gammaCoordinateDensityObject (e := k) (k := 0) hc C₀ R hCC₀
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)).extend hCD),
      f.GammaDefinable B := by
  intro Z R
  let e := FiniteRV.gammaRawFiniteNormalizationIso hκ hs hreal hBC hU hfin T hT
  have hold (u : rvObjectDomain Z.object) :
      (e.equiv u).val (FiniteRV.contractionOldLabelIndex T δ) = u.val (suffixIndex T.program.rvArity_le δ) :=
    toFirstVolume_oldLabels _ _ _ _
  have hZ : ∀ u : rvObjectDomain Z.object, (u.val (suffixIndex T.program.rvArity_le δ)).val ≠ iRVZero := by
    intro u
    rw [← hold]
    exact normalized_contraction_retained_density_nonzero T δ hδ (e.equiv u)
  have hcoord (u : rvObjectDomain Z.object) :
      gammaVolumeValue R.toGammaRVObject (e.equiv u) = gammaVolumeValue Z.toGammaRVObject u :=
    toFirstVolume_volume _ _ _
  obtain ⟨D,hCD,f,hf⟩ := gamma_coordinate_density_equivalence_realize hc C₀ Z R hCC₀ hCC₀
    (suffixIndex T.program.rvArity_le δ) (FiniteRV.contractionOldLabelIndex T δ) hZ
    (normalized_contraction_retained_density_nonzero T δ hδ) e hcoord hold
  exact ⟨hZ,D,hCD,f,hf⟩

end IntegrationInACVF.Section7
