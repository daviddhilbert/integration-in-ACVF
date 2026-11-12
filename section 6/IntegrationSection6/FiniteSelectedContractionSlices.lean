import IntegrationSection6.FiniteSelectedContractions
import IntegrationSection6.GammaSwappedVolumes
import IntegrationSection6.GammaNamedIsoRestrictions
import IntegrationSection6.GammaSelectedLiftSlices

/-! Selected-volume slices of actual standard contractions have lifts
isomorphic to the original set with the selected old RV labels fixed. -/
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

theorem contraction_selected_lift_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin (n+C.arity) → RV (M := M) |
        (x,r) ∈ (C.gammaNormalizedObject hBS (gamma_program_final_set C.program hC)).lift ∧
        r ∘ (fun j => contractionOldLabelIndex C (ρ j)) = t}.Finite := by
  let f := C.gammaNormalizedLiftIso hBS hA hC
  apply finite_selected_rv_fibres_of_gammaIso hκ hs hsmall f ρ _ ?_ hfin
  intro a
  change (C.normalizedNaturalLiftMap a).val.2 ∘ _ = _
  rw [C.normalizedNaturalLiftMap_square]
  exact contraction_selectedLabels C ρ a

def gammaPrependSelectedContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVFiniteObject B (e+n) :=
  gammaPrependSelectedVolume (C.gammaNormalizedObject hBS (gamma_program_final_set C.program hC))
    (fun j => contractionOldLabelIndex C (ρ j))
    (contraction_selected_lift_finite hκ hs hsmall hBS hA ρ hfin C hC)

def gammaSelectedContractionSliceLiftIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin e → Fin m)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin e → RV (M := M)),
      {r : Fin m → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) (t : Fin e → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (n+C.arity) n
      ((gammaVolumeSliceSchema (gammaPrependSelectedContraction hκ hs hsmall hBS hA ρ hfin C hC)).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaPrependSelectedContraction hκ hs hsmall hBS hA ρ hfin C hC)).rowVolume (fun j => (t j).val))) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (carrier A ∩ {p | p.2 ∘ ρ = t}) P.toGamma.lift := by
  let U := C.gammaNormalizedObject hBS (gamma_program_final_set C.program hC)
  let f := C.gammaNormalizedLiftIso hBS hA hC
  let τ := fun j => contractionOldLabelIndex C (ρ j)
  have hLabels (a : A) : (f.equiv a).val.2 ∘ τ = a.val.2 ∘ ρ := by
    change (C.normalizedNaturalLiftMap a).val.2 ∘ τ = _
    rw [C.normalizedNaturalLiftMap_square]
    exact contraction_selectedLabels C ρ a
  let f' := gammaIsoNamedRVLabels f ρ τ hLabels t
  let g := gammaSelectedSliceLiftIso U τ (contraction_selected_lift_finite hκ hs hsmall hBS hA ρ hfin C hC) t P
  exact f'.trans (gammaLogicInput _) g

end IntegrationInACVF.Section6.FiniteRV
