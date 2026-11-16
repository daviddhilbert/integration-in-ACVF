module

public import Integration7.HeadAppendVolumeCoordinates
public import Integration7.GammaEqualLabelEquivalenceGraphs
public import Integration7.UnarySelectedNormalizationVolumeIso
public import IntegrationSection6.RawContractionDomain

@[expose] public section

/-! The unnormalized unary contraction of a frozen head fibre is the
actual head-contracted RV fibre, retaining old selected coordinates first. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Section4.vfSpace
  SpecialTransformations.Section4.rvSpace SpecialTransformations.Milestone0.sortEval
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S (n+1) a}

theorem head_coordinate_fibre_base (S : Set M) (x : Fin n → VF (M := M)) :
    coordinateFibreBase S 0 (headFrozenTuple x) = S ∪ Set.range (fun j => (x j).val) :=
  congrArg Base.real (coordinateGammaBase_head (B := ⟨S,∅⟩) x)

def headFibreRawVolumeObject {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M)) :
    GammaRVFiniteObject ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ ((k+1)+1) :=
  gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs
    (small_union_range hκ B.real hreal (fun j => (x j).val))
    (by rw [head_coordinate_fibre_base]; exact Set.union_subset_union hBS (Set.Subset.refl _))
    (gamma_head_fibre U hU x) ρ (headFibre_selected_finite U ρ hfin x)
    (headCoordinateFibreContraction T x) (gamma_head_coordinate_fibre_contraction T hT hTarget x))

theorem head_fibre_raw_domain {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
    (r : Fin (1+T.arity) → RV (M := M)) :
    r ∈ @SpecialTransformations.DefinableGeometry.DefSet.carrier LRV M (@CanonicalStructure.normalize M sM) _ _
      (rvObjectDomain (headFibreRawVolumeObject hκ hs hreal hBS hU ρ hfin T hT hTarget x).object) ↔
      (x,r) ∈ carrier T.contractedSet :=
  (rawContractionDomain_iff (headCoordinateFibreContraction T x) (Fin.elim0,r)).trans
    (head_coordinate_fibre_contraction_domain T x r)

theorem head_fibre_raw_volume {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBS : B.real ⊆ S) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target)) (x : Fin n → VF (M := M))
    (r : rvObjectDomain (headFibreRawVolumeObject hκ hs hreal hBS hU ρ hfin T hT hTarget x).object) :
    gammaVolumeValue (headFibreRawVolumeObject hκ hs hreal hBS hU ρ hfin T hT hTarget x).toGammaRVObject r =
      r.val ∘ headAppendVolumeIndex T ρ := by
  let C := headCoordinateFibreContraction T x
  change Fin.append (r.val ∘ C.volumeIndex) (fun j => r.val (suffixIndex C.program.rvArity_le (ρ j))) ∘
    (@finAddFlip (k+1) 1) = _
  rw [append_finAddFlip]
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left,Function.comp_apply,headAppendVolumeIndex,headSelectedLabelIndex]
    exact congrArg r.val (head_coordinate_fibre_old_label_index T x (ρ i))
  · simp only [Fin.append_right,Function.comp_apply,headAppendVolumeIndex]
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact congrArg r.val (head_coordinate_fibre_volume_index T x)

end IntegrationInACVF.Section7
