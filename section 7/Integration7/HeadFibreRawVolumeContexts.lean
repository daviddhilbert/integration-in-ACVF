module

public import Integration7.HeadFibreRawVolumeEquivalence
public import Integration7.RawSelectedContractionParameterExtension
public import Integration7.GammaCoordinateDensityEquivalences
public import Integration7.SelectedCoordinateDensityRows

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Realize the actual head fibre as the raw selected unary contraction
in any containing context, preserving full volume and density data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a k : ℕ}

set_option maxHeartbeats 2400000 in
theorem head_fibre_raw_volume_context_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D C₀ : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (hU : GammaSetDefinable B (carrier U))
    (ρ : Fin (k+1) → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin (k+1) → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target))
    (δ : Fin a) (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (x : Fin n → VF (M := M))
    (hRD : coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) ⊆ (D.base : Set M))
    (hDC₀ : (D.base : Set M) ⊆ (C₀.base : Set M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headAppendVolumeIndex T ρ) x)
    (hPC₀ : P.codes ⊆ (C₀.base : Set M)) :
    let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
    let hBR : Bx.real ⊆ coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) :=
      by rw [head_coordinate_fibre_base];exact Set.union_subset_union hBC (Set.Subset.refl _)
    let TD := (headCoordinateFibreContraction T x).extendBase hRD
    let hTD := (headCoordinateFibreContraction T x).program.extendBase_gamma hRD
      (gamma_head_coordinate_fibre_contraction T hT hTarget x)
    let W := gammaSwapVolumeBlocks (FiniteRV.gammaRawSelectedContraction hκ hs
      (small_union_range hκ B.real hreal (fun j => (x j).val)) (hBR.trans hRD)
      (gamma_head_fibre U hU x) ρ (headFibre_selected_finite U ρ hfin x) TD hTD)
    ∀ hW : ∀ u : rvObjectDomain W.object, (u.val (suffixIndex TD.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ E : BaseContext M, ∃ hC₀E : (C₀.base : Set M) ⊆ (E.base : Set M),
    ∃ f : RVVolumeIso
      ((gammaCoordinateDensityObject (e := k+1) (k := 0) hc C₀ P.toGamma hPC₀
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
        (selected_fibre_retained_density_nonzero T.contractedSet (headAppendVolumeIndex T ρ) _
          (head_retained_density_nonzero T δ hδ) x P)).extend hC₀E)
      ((gammaCoordinateDensityObject (e := k+1) (k := 0) hc C₀ W hDC₀
        (suffixIndex TD.program.rvArity_le δ) hW).extend hC₀E), f.GammaDefinable Bx := by
  intro Bx hBR TD hTD W hW
  obtain ⟨e,hcoord,he⟩ := head_fibre_raw_volume_equivalence hκ hs hreal hBC hU ρ hfin T hT hTarget x P
  obtain ⟨d,hdcoord,hd⟩ := raw_selected_contraction_extension_equivalence hκ hs
    (small_union_range hκ B.real hreal (fun j => (x j).val)) hBR hRD
    (coordinateFibre U 0 (headFrozenTuple x)) (gamma_head_fibre U hU x) ρ
    (headFibre_selected_finite U ρ hfin x) (headCoordinateFibreContraction T x)
    (gamma_head_coordinate_fibre_contraction T hT hTarget x)
  let f := FiniteRV.gammaIsoTrans e d
  have hcoord' (u : P.domain) : gammaVolumeValue W.toGammaRVObject (f.equiv u) =
      gammaVolumeValue P.toGamma.toGammaRVObject u := (hdcoord (e.equiv u)).trans (hcoord u)
  have hDensity (u : P.domain) : (f.equiv u).val (suffixIndex TD.program.rvArity_le δ) =
      u.val (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) := by
    have hl : (f.equiv u).val = u.val := (hd (e.equiv u)).trans (he u)
    rw [hl]
    exact congrArg u.val (head_coordinate_fibre_old_label_index T x δ)
  exact gamma_coordinate_density_equivalence_realize hc C₀ P.toGamma W hPC₀ hDC₀ _ _
    (selected_fibre_retained_density_nonzero T.contractedSet (headAppendVolumeIndex T ρ) _
      (head_retained_density_nonzero T δ hδ) x P) hW f hcoord' hDensity

end IntegrationInACVF.Section7
