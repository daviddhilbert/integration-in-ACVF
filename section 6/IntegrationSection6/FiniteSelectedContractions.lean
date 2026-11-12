import IntegrationSection6.GammaSelectedVolumeObjects
import IntegrationSection6.GammaRelativeRVFiniteness
import IntegrationSection6.FiniteContractionLabels

/-! The E union I_n contraction object under the exact selected-label
finiteness hypothesis: fixing VF and the selected original RV labels has
finite fibres. All old RV labels together may have infinite fibres. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m e : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m} {σ : Equiv.Perm (Fin n)}

def gammaFiniteSelectedContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVFiniteObject B (n+e) := by
  let U := C.gammaNormalizedObject hBS (gamma_program_final_set C.program hC)
  let f := C.gammaNormalizedLiftIso hBS hA hC
  let τ := fun j => contractionOldLabelIndex C (ρ j)
  have hLabels (a : A) : (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ := by
    change (C.normalizedNaturalLiftMap a).val.2 ∘ τ = _
    rw [C.normalizedNaturalLiftMap_square]
    exact contraction_selectedLabels C ρ a
  exact gammaFiniteSelectedVolume U τ
    (finite_selected_rv_fibres_of_gammaIso hκ hs hsmall f ρ τ hLabels hfin)

theorem gammaFiniteSelectedContraction_object {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    (gammaFiniteSelectedContraction hκ hs hsmall hBS hA ρ hfin C hC).object =
      appendSelectedVolumeObject C.normalizedObject (fun j => contractionOldLabelIndex C (ρ j)) := rfl

theorem gammaFiniteSelectedContraction_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) (a : A) :
    (rvObjectVolume (gammaFiniteSelectedContraction hκ hs hsmall hBS hA ρ hfin C hC).object
      (C.normalizedContractionMap a)).val =
        Fin.append (rvObjectVolume C.normalizedObject (C.normalizedContractionMap a)).val
          (fun j => a.val.2 (ρ j)) := by
  change Fin.append _ _ = Fin.append _ _
  exact congrArg (Fin.append _) (contraction_selectedLabels C ρ a)

end IntegrationInACVF.Section6.FiniteRV
