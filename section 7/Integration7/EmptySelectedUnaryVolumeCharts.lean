module

public import Integration7.FiniteContractionNormalizationVolumeIso
public import Integration7.EmptySelectedVolumeCharts
public import Integration7.GammaVolumeSliceAssemblyGeometry
public import IntegrationSection6.FiniteSelectedContractionSlices

@[expose] public section

/-! With no old selected volume, the selected unary object and the ordinary
normalized finite contraction have identical labels, volume and density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a : ℕ}

theorem empty_selected_unary_volume_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C C₀ : BaseContext M)
    (hCC₀ : (C.base : Set M) ⊆ (C₀.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) 1 a) (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin 1 → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    {σ : Equiv.Perm (Fin 1)} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ q : U, (q.val.2 δ).val ≠ iRVZero) :
    let P := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hU hfin T hT
    let Q := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU
      (Fin.elim0 : Fin 0 → Fin a) (empty_selected_volume_finite U hfin) T hT
    ∃ e : RVVolumeIso
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ Q hCC₀
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ))
      (gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ P hCC₀
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)),
      e.GammaDefinable B := by
  intro P Q
  let V := gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ Q hCC₀
    (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)
  let W := gammaCoordinateDensityObject (e := 0) (k := 0) hc C₀ P hCC₀
    (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)
  let f : Map V.underlying.obj.domain W.underlying.obj.domain := Map.id _
  have hCoord : ∀ u, W.underlying.obj.value (f u) = V.underlying.obj.value u := by
    intro u
    funext i
    apply Subtype.ext
    change (gammaVolumeValue P.toGammaRVObject ⟨u.val,u.property⟩ i).val =
      (gammaVolumeValue Q.toGammaRVObject ⟨u.val,u.property⟩ i).val
    change (gammaVolumeValue (T.gammaNormalizedObject hBC (gamma_program_final_set T.program hT))
        ⟨u.val,u.property⟩ i).val = _
    dsimp only [Q, FiniteRV.gammaPrependSelectedContraction]
    rw [gammaPrependSelectedVolume_value]
    have hi : i = Fin.natAdd 0 i := by ext; simp
    conv_rhs => rw [hi, Fin.append_right]
  let e := RVVolumeIso.of_preserving_coordinates_full hc C₀
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f Function.bijective_id hCoord)) hCoord (fun _ => rfl)
  exact ⟨e,gamma_volume_iso_of_label_identity hc e
    (gamma_coordinate_density_object_graphs (e := 0) (k := 0) hc C₀ Q hCC₀ _
      (normalized_contraction_retained_density_nonzero T δ hδ)) rfl (fun _ => rfl)⟩

end IntegrationInACVF.Section7
