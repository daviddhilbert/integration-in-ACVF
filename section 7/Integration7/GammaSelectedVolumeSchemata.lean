import Integration7.TypedVolumeDensityValidity
import Integration7.NonzeroDensityFormulas
import IntegrationSection6.GammaSelectedLabelFamilies

/-! Selected coordinate maps and an actual retained nonzero density
label form full original-Gamma volume schemata over VF parameters. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {p a k : ℕ}

def gammaSelectedVolumeSchema (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a) (δ : Fin a) :
    GammaRVVolumeSchema B p a k (fun _ => .vf) where
  object := gammaSelectedLabelSchema U hU ρ
  density := nonzeroDensityFormula (gammaSelectedLabelSchema U hU (fun _ : Fin 1 => δ)).volume
  density_definable := nonzeroDensityFormula_definable
    (gammaSelectedLabelSchema U hU (fun _ : Fin 1 => δ)).volume_definable
  density_nonzero _ h := h.2

theorem gammaSelectedVolumeSchema_density (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hNZ : ∀ x ∈ carrier U, (x.2 δ).val ≠ iRVZero) (x : Fin p → VF (M := M))
    (r : Fin a → RV (M := M)) (y : Fin 1 → RV (M := M)) :
    (gammaSelectedVolumeSchema U hU ρ δ).rowDensity (fun j => (x j).val) r y ↔
      (x,r) ∈ carrier U ∧ (fun _ : Fin 1 => r δ) = y := by
  change Fin.append (Fin.append _ _) _ ∈ nonzeroDensityFormula _ ↔ _
  rw [nonzeroDensityFormula_append]
  have hv := gammaSelectedLabelSchema_volume U hU (fun _ : Fin 1 => δ) x r y
  constructor
  · intro h
    exact hv.mp h.1
  · intro h
    refine ⟨hv.mpr h,?_⟩
    have hy : y 0 = r δ := congrFun h.2.symm 0
    change (y 0).val ≠ iRVZero
    rw [hy]
    exact hNZ (x,r) h.1

theorem gammaSelectedVolumeSchema_density_valid (U : DefSet (M := M) S p a)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin (k+1) → Fin a) (δ : Fin a)
    (hNZ : ∀ x ∈ carrier U, (x.2 δ).val ≠ iRVZero) (x : Fin p → VF (M := M)) :
    functionMapRowValid (fun _ => .vf) (gammaSelectedVolumeSchema U hU ρ δ).object.domain
      (gammaSelectedVolumeSchema U hU ρ δ).density (fun j => (x j).val) := by
  let F := gammaSelectedVolumeSchema U hU ρ δ
  have hD := gammaSelectedLabelSchema_domain U hU ρ x
  have hρ := gammaSelectedVolumeSchema_density U hU ρ δ hNZ x
  apply F.density_valid_of_typed _ (fun j => (x j).property)
  · intro r hr
    have hr' : (x,r) ∈ carrier U := (Set.ext_iff.mp hD r).mp hr
    exact ⟨fun _ => r δ,(hρ r _).mpr ⟨hr',rfl⟩,fun y hy => ((hρ r y).mp hy).2.symm⟩
  · intro r y hy
    exact (Set.ext_iff.mp hD r).mpr ((hρ r y).mp hy).1

end IntegrationInACVF.Section7
