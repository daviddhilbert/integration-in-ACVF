import Integration7.FixedLabelTranslationDensityForms
import Integration7.GeometricFiniteStandardVolumeComparisons

/-! Actual normalized finite contraction volume objects of a pure VF
domain with fixed old labels and a selected retained nonzero density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {n d : ℕ}

def fixedLabelContractionGammaObject {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hPC : P.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (n+1) 0) (hA : GammaSetDefinable P (carrier A))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη0 : η ≠ 0)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (hT : GammaProgramDefinable P T.program) : GammaVolumeObjects P (C.base : Set M) n :=
  let U := FiniteRV.gammaFiniteContraction hκ hs hreal hPC
    (gamma_fixed_rv_label_domain A hA z hz hzΓ) (fixed_pure_rv_label_fibres_finite A z hz) T hT
  let hNZ := normalized_contraction_retained_density_nonzero T (Fin.natAdd 0 j)
    (fun p => raw_fixed_rv_label_density_nonzero hc A z hz j η hj hη0 ⟨p.val,p.property⟩)
  ⟨gammaCoordinateDensityObject (e := n) (k := 0) hc C U (Set.Subset.refl _)
      (FiniteRV.contractionOldLabelIndex T (Fin.natAdd 0 j)) hNZ,
    gamma_coordinate_density_object_graphs hc C U (Set.Subset.refl _) _ _⟩

end IntegrationInACVF.Section7
