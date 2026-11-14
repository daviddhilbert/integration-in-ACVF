import Integration7.HeadFiniteRawVolumeEquivalence
import Integration7.RawFiniteContractionParameterExtension
import Integration7.GammaCoordinateDensityEquivalences
import Integration7.SelectedCoordinateDensityRows
import Integration7.HeadAppendVolumeCoordinates

/-! The first head RV[1] fibre and its actual raw unary contraction have
an original-Gamma volume isomorphism preserving the retained density.
No old selected-coordinate hypothesis is imposed on this first step. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

set_option maxHeartbeats 1600000 in
theorem head_finite_volume_context_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D C₀ : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin (n+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (T : HeadPreparation U) (hT : GammaGraphDefinable B (pointMapGraph T.map))
    (hTarget : GammaSetDefinable B (carrier T.target))
    (δ : Fin a) (hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero)
    (x : Fin n → VF (M := M))
    (hRD : coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) ⊆ (D.base : Set M))
    (hDC₀ : (D.base : Set M) ⊆ (C₀.base : Set M))
    (P : SelectedLabelFibrePresentation B T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) x)
    (hPC₀ : P.codes ⊆ (C₀.base : Set M)) :
    let Bx : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
    let hBR : Bx.real ⊆ coordinateFibreBase (C.base : Set M) 0 (headFrozenTuple x) := by
      rw [head_coordinate_fibre_base];exact Set.union_subset_union hBC (Set.Subset.refl _)
    let TX := headCoordinateFibreContraction T x
    let TD := TX.extendBase hRD
    let W := FiniteRV.gammaRawFiniteContraction hκ hs
      (small_union_range hκ B.real hreal (fun j => (x j).val)) (hBR.trans hRD) (gamma_head_fibre U hU x)
      (head_coordinate_fibre_finite_labels hfin x) TD
      (TX.program.extendBase_gamma hRD (gamma_head_coordinate_fibre_contraction T hT hTarget x))
    ∀ hW : ∀ u : rvObjectDomain W.object, (u.val (suffixIndex TD.program.rvArity_le δ)).val ≠ iRVZero,
    ∃ (E : BaseContext M) (hC₀E : (C₀.base : Set M) ⊆ (E.base : Set M)),
    ∃ f : RVVolumeIso
      ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ P.toGamma hPC₀
        (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ))
        (selected_fibre_retained_density_nonzero (k := 0) T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _
          (head_retained_density_nonzero T δ hδ) x P)).extend hC₀E)
      ((gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ W hDC₀
        (suffixIndex TD.program.rvArity_le δ) hW).extend hC₀E), f.GammaDefinable Bx := by
  intro Bx hBR TX TD W hW
  obtain ⟨e,hcoord,he⟩ := head_finite_raw_volume_equivalence hκ hs hreal hBC hU hfin T hT hTarget x P
  obtain ⟨d,hdcoord,hd⟩ := raw_finite_contraction_extension_equivalence hκ hs
    (small_union_range hκ B.real hreal (fun j => (x j).val)) hBR hRD
    (coordinateFibre U 0 (headFrozenTuple x)) (gamma_head_fibre U hU x)
    (head_coordinate_fibre_finite_labels hfin x) TX (gamma_head_coordinate_fibre_contraction T hT hTarget x)
  let f := FiniteRV.gammaIsoTrans e d
  have hcoord' (u : P.domain) : gammaVolumeValue W.toGammaRVObject (f.equiv u) =
      gammaVolumeValue P.toGamma.toGammaRVObject u := (hdcoord (e.equiv u)).trans (hcoord u)
  have hDensity (u : P.domain) : (f.equiv u).val (suffixIndex TD.program.rvArity_le δ) =
      u.val (Fin.natAdd 1 (suffixIndex (specialRelative_rvArity_le T.special) δ)) := by
    have hlabels : (f.equiv u).val = u.val := (hd (e.equiv u)).trans (he u)
    rw [hlabels]
    exact congrArg u.val (head_coordinate_fibre_old_label_index T x δ)
  exact gamma_coordinate_density_equivalence_realize hc C₀ P.toGamma W hPC₀ hDC₀ _ _
    (selected_fibre_retained_density_nonzero (k := 0) T.contractedSet (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)) _
      (head_retained_density_nonzero T δ hδ) x P) hW f hcoord' hDensity

end IntegrationInACVF.Section7
