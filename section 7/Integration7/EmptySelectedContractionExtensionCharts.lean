import Integration7.GammaVolumeSliceAssemblyGeometry
import Integration7.NormalizedContractionParameterExtension
import Integration7.GammaVolumeSliceDensityAssembly
import IntegrationSection6.FiniteSelectedContractionSlices

/-! Parameter enlargement preserves an actual finite contraction with no
old selected volume, including its retained density and original-Gamma chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open SpecialTransformations.Section7 (gammaVolumeValue)
open SpecialTransformations.DefinableGeometry
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

set_option maxHeartbeats 1600000 in
def emptySelectedContractionExtensionVolumeIso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D E : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hDE : (D.base : Set M) ⊆ (E.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin 0 → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ u : U, (u.val.2 δ).val ≠ iRVZero) :
    let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT
    let TD := T.extendBase hCD
    let RD := FiniteRV.gammaPrependSelectedContraction hκ hs hreal (hBC.trans hCD) hU ρ hfin TD
      (T.program.extendBase_gamma hCD hT)
    RVVolumeIso
      (gammaCoordinateDensityObject (e := 0) (k := n) hc E RU (hCD.trans hDE)
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ))
      (gammaCoordinateDensityObject (e := 0) (k := n) hc E RD hDE
        (FiniteRV.contractionOldLabelIndex TD δ) (normalized_contraction_retained_density_nonzero TD δ hδ)) := by
  intro RU TD RD
  let A := gammaCoordinateDensityObject (e := 0) (k := n) hc E RU (hCD.trans hDE)
    (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)
  let V := gammaCoordinateDensityObject (e := 0) (k := n) hc E RD hDE
    (FiniteRV.contractionOldLabelIndex TD δ) (normalized_contraction_retained_density_nonzero TD δ hδ)
  have hDom := T.extendBase_normalized_domain hCD
  let f : Map A.underlying.obj.domain V.underlying.obj.domain :=
    Map.inclusion (fun _ h => hDom.ge h)
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Subtype.ext
      exact congrArg (fun w : V.underlying.obj.domain => w.val) huv
    · intro v
      exact ⟨⟨v.val,hDom.le v.property⟩,rfl⟩
  have hcoord : ∀ u, V.underlying.obj.value (f u) = A.underlying.obj.value u := fun _ => rfl
  exact RVVolumeIso.of_preserving_coordinates_full hc E
    (rvFiniteIsoOfAmbient (rvIsoOfVolumePreservingBijection f hf hcoord)) hcoord (fun _ => rfl)

set_option maxHeartbeats 1600000 in
theorem gamma_empty_selected_contraction_extension_iso {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C D E : BaseContext M)
    (hCD : (C.base : Set M) ⊆ (D.base : Set M)) (hDE : (D.base : Set M) ⊆ (E.base : Set M))
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hBC : B.real ⊆ (C.base : Set M))
    (U : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) (n+1) a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin 0 → Fin a)
    (hfin : ∀ (x : Fin (n+1) → VF (M := M)) (t : Fin 0 → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction U σ) (hT : GammaProgramDefinable B T.program)
    (δ : Fin a) (hδ : ∀ u : U, (u.val.2 δ).val ≠ iRVZero) :
    (emptySelectedContractionExtensionVolumeIso hc C D E hCD hDE hκ hs hreal hBC U hU ρ hfin T hT δ hδ).GammaDefinable B := by
  let RU := FiniteRV.gammaPrependSelectedContraction hκ hs hreal hBC hU ρ hfin T hT
  let e := emptySelectedContractionExtensionVolumeIso hc C D E hCD hDE hκ hs hreal hBC U hU ρ hfin T hT δ hδ
  have hA : VolumeObjectGamma
      (gammaCoordinateDensityObject (e := 0) (k := n) hc E RU (hCD.trans hDE)
        (FiniteRV.contractionOldLabelIndex T δ) (normalized_contraction_retained_density_nonzero T δ hδ)) B :=
    gamma_coordinate_density_object_graphs (e := 0) (k := n) hc E RU
      (hCD.trans hDE) (FiniteRV.contractionOldLabelIndex T δ)
      (normalized_contraction_retained_density_nonzero T δ hδ)
  exact gamma_volume_iso_of_label_identity hc e hA rfl (fun _ => rfl)

end IntegrationInACVF.Section7
