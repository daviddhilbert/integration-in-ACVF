module

public import Integration7.GeometricFiniteStandardVolumeComparisons

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! The actual normalized contraction object for any finite-label
positive VF domain with a retained nonzero density coordinate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {k a : ℕ}

def retainedDensityContractionGammaObject {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hBC : B.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (k+1) a) (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin (k+1) → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (δ : Fin a) (hδ : ∀ p : A, (p.val.2 δ).val ≠ iRVZero)
    {σ : Equiv.Perm (Fin (k+1))} (T : StandardContraction A σ) (hT : GammaProgramDefinable B T.program) :
    GammaVolumeObjects B (C.base : Set M) k :=
  let U := FiniteRV.gammaFiniteContraction hκ hs hreal hBC hA hfin T hT
  let hNZ := normalized_contraction_retained_density_nonzero T δ hδ
  ⟨gammaCoordinateDensityObject (e := k) (k := 0) hc C U (Set.Subset.refl _)
      (FiniteRV.contractionOldLabelIndex T δ) hNZ,
    gamma_coordinate_density_object_graphs hc C U (Set.Subset.refl _) _ _⟩

end IntegrationInACVF.Section7
