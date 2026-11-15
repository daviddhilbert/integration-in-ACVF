import Integration7.FixedLabelContractionVolumeObjects
import Integration7.TwoOrderProductCoordinateDensities

/-! For any actual standard contraction of a pure VF domain with fixed
labels, the retained selected density is exactly the same constant on
its entire normalized RV domain. -/
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

theorem fixed_label_contraction_constant_density {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hreal : Cardinal.mk P.real < κ)
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M) (hPC : P.real ⊆ (C.base : Set M))
    (A : DefSet (M := M) (C.base : Set M) (n+1) 0) (hA : GammaSetDefinable P (carrier A))
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ (C.base : Set M))
    (hzΓ : DefinableOverBase P (fun _ : Fin d => .rv) {fun j => (z j).val})
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) (hη : η.val ∈ C.base) (hη0 : η ≠ 0)
    {σ : Equiv.Perm (Fin (n+1))} (T : StandardContraction (fixedRVLabelDomain A z hz) σ)
    (hT : GammaProgramDefinable P T.program)
    (hF : (canonicalRVObject hc T.contractionObject).volume.FiniteFibres) :
    (fixedLabelContractionGammaObject hκ hs hreal hc C hPC A hA z hz hzΓ j η hj hη0 T hT).val =
      (normalizedUnitVolumeContraction hc T hF).rescale η hη hη0 := by
  obtain ⟨hε,hEq⟩ := normalized_contraction_coordinate_density_eq_constant hc T hF (Fin.natAdd 0 j)
    η hη hη0 (fixed_rv_label_domain_retained_value A z hz j η hj)
  exact hEq

end IntegrationInACVF.Section7
