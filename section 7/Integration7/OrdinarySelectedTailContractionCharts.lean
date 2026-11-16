module

public import Integration7.OrdinarySelectedPresentationMaps
public import Integration7.OrdinarySelectedTailWeightSelectors

@[expose] public section

/-! The VF-tail realization gives a genuine ordinary RV isomorphism
from a completed lifted contraction to the original selected contraction.
No essential restriction or density form occurs in this comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5 IntegrationInACVF.Section6
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a d r : ℕ}
variable {A : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

theorem selected_tail_ordinary_degree_eq : orderedVolumeDegree (d+n) 0 = orderedVolumeDegree n d := by
  rw [orderedVolumeDegree_eq,orderedVolumeDegree_eq]
  omega

theorem selected_tail_ordered_weight (hc : CanonicalStructure.IsCanonical (M := M))
    (T : StandardContraction A σ) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (v : V) :
    rawWeight (fun j => (v.val.2 (orderedSelectedIndex (selectedRVVFTailStandardContraction hc T ρ E).program
      (Fin.elim0 : Fin 0 → Fin a) j)).val) =
    rawWeight (fun j => ((canonicalSelectedTailRVProjection hc T.target
      (suffixIndex T.program.rvArity_le ∘ ρ) E v).val.2 (orderedSelectedIndex T.program ρ j)).val) := by
  rw [standard_empty_selected_weight]
  let f := canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E
  have hcoord := selected_rv_vf_tail_standard_volume hc T ρ E hVF v
  have hw := congrArg (fun z : Fin (d+n) → RV (M := M) => rawWeight (fun j => (z j).val)) hcoord
  exact hw.symm.trans (standard_selected_volume_weight T ρ (f v).val.2)

def selectedTailOrdinaryContractionIso (hc : CanonicalStructure.IsCanonical (M := M))
    (T : StandardContraction A σ) (ρ : Fin d → Fin a) {V : DefSet (M := M) S 0 r}
    (E : OrderedContractionProgram S (nativeProgramSelectedRVVFTailLift (n := 0) (d := d)
      hc T.target (suffixIndex T.program.rvArity_le ∘ ρ)) V)
    (hVF : ∀ p, (E.naturalMap p).val.1 = p.val.1) (hCon : Contractible E.toMap)
    (hV : GammaSetDefinable B (carrier V))
    (P : GammaSelectedRVPresentation B V
      (orderedSelectedIndex (selectedRVVFTailStandardContraction hc T ρ E).program (Fin.elim0 : Fin 0 → Fin a)))
    (Q : GammaSelectedRVPresentation B T.target (orderedSelectedIndex T.program ρ)) :
    SpecialTransformations.Section7.GammaRVIso P.toGamma.toGammaRVObject
      (gammaCastDegree (selected_tail_ordinary_degree_eq (d := d) (n := n)).symm Q.toGamma).toGammaRVObject :=
  selectedRVPresentationMapIsoOfEqualDegree selected_tail_ordinary_degree_eq _ _
    (canonicalSelectedTailRVProjection hc T.target (suffixIndex T.program.rvArity_le ∘ ρ) E)
    (canonical_selected_tail_rv_projection_bijective hc T.target _ E hCon)
    (gamma_canonical_selected_tail_rv_projection hc T.target _ E hV)
    (selected_tail_ordered_weight hc T ρ E hVF) P Q
end IntegrationInACVF.Section7
