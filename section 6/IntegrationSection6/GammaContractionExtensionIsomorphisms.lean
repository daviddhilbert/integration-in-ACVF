import IntegrationSection6.ContractionExtensionIndices
import IntegrationSection6.GammaContractionPresentationIsomorphisms
import IntegrationSection6.GammaPermutedFibrePresentations
import IntegrationSection6.EmptySelectedContractions

/-! Internal real presentation extension preserves the actual finite
contraction object up to a full original-Gamma RV isomorphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S R : Set M} {n a k : ℕ}
variable {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def gammaSelectedContractionExtensionIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S) (hSR : S ⊆ R)
    (hA : GammaSetDefinable B (carrier A)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier A ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVIso (gammaFiniteSelectedContraction hκ hs hreal hBS hA ρ hfin C hC).toGammaRVObject
      (gammaFiniteSelectedContraction hκ hs hreal (Set.Subset.trans hBS hSR) hA ρ hfin
        (extendStandardContraction C hSR) (gamma_extendStandardContraction C hSR hC)).toGammaRVObject := by
  let E := extendStandardContraction C hSR
  let hE := gamma_extendStandardContraction C hSR hC
  let P := Classical.choice (gammaSelectedRVPresentation_exists C.target (gamma_program_final_set C.program hC)
    (orderedSelectedIndex C.program ρ)
    (ordered_selected_fibres_finite hκ hs hreal C.program hC ρ (vfPermutation_selected_finite A σ ρ hfin)))
  have hIdx : orderedSelectedIndex E.program ρ = orderedSelectedIndex C.program ρ :=
    extendContractionProgram_selectedIndex C.program hSR ρ
  let P' : GammaSelectedRVPresentation B E.target (orderedSelectedIndex E.program ρ) :=
    P.congrFormula rfl (fun r y => and_congr Iff.rfl
      (Iff.of_eq (congrArg (fun θ => r ∘ θ = y) hIdx.symm)))
  let e := gammaContractionPresentationIso hκ hs hreal hBS hA ρ hfin C hC P
  have f := gammaContractionPresentationIso hκ hs hreal (Set.Subset.trans hBS hSR) hA ρ hfin E hE P'
  have f' : GammaRVIso P.toGamma.toGammaRVObject
      (gammaCastDegree (orderedVolumeDegree_eq n k).symm
        (gammaFiniteSelectedContraction hκ hs hreal (Set.Subset.trans hBS hSR) hA ρ hfin E hE)).toGammaRVObject := by
    simpa only [P',GammaFiniteGraphPresentation.congrFormula_toGamma] using f
  have g := gammaRVIsoCastDegree (orderedVolumeDegree_eq n k) (gammaIsoTrans (gammaIsoSymm e) f')
  simpa only [gammaCastDegree_symm] using g

def gammaContractionExtensionIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S) (hSR : S ⊆ R)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVIso (gammaFiniteContraction hκ hs hreal hBS hA hfin C hC).toGammaRVObject
      (gammaFiniteContraction hκ hs hreal (Set.Subset.trans hBS hSR) hA hfin
        (extendStandardContraction C hSR) (gamma_extendStandardContraction C hSR hC)).toGammaRVObject :=
  gammaIsoTrans (gammaIsoSymm (gammaEmptySelectedContractionIso hκ hs hreal hBS hA hfin C hC))
    (gammaIsoTrans (gammaSelectedContractionExtensionIso hκ hs hreal hBS hSR hA Fin.elim0
      (empty_selected_fibres A hfin) C hC)
      (gammaEmptySelectedContractionIso hκ hs hreal (Set.Subset.trans hBS hSR) hA hfin
        (extendStandardContraction C hSR) (gamma_extendStandardContraction C hSR hC)))

end IntegrationInACVF.Section6.FiniteRV
