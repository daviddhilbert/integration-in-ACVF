module

public import Integration7.TwoOrderProductNormalization
public import Integration7.ConstantCoordinateDensityObjects

@[expose] public section

/-! A density contained in the fixed old label tuple becomes the exact
retained coordinate density on both actual normalized product objects. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n a d : ℕ}

theorem fixed_rv_label_domain_retained_value (A : DefSet (M := M) S n a)
    (z : Fin d → RV (M := M)) (hz : ∀ j, (z j).val ∈ S)
    (j : Fin d) (η : RV (M := M)) (hj : z j = η) :
    ∀ p : fixedRVLabelDomain A z hz, p.val.2 (Fin.natAdd a j) = η := by
  intro p
  exact (congrFun ((fixed_rv_label_domain_carrier A z hz p.val).mp p.property).2 j).trans hj

namespace TwoOrderProductPreparations
variable {P : Base (M := M)} {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (F : TwoOrderProductPreparations X Y D E r t z hz P)

theorem head_normalized_coordinate_density (hr : r.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    let U := (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0).underlying
    let ε := FiniteRV.contractionOldLabelIndex F.headContraction (Fin.natAdd 0 j)
    ∃ hε : ∀ u : U.obj.domain, u.val ε ≠ 0,
      coordinateDensityVolumeObject U ε hε = F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0 := by
  exact normalized_contraction_coordinate_density_eq_constant hc F.headContraction
    (F.headRawFiniteRVObject hκ hs hsmall hc hr).property (Fin.natAdd 0 j) η (F.contains hη) hη0
    (fixed_rv_label_domain_retained_value (extendBase X F.contains) z (fun j => F.contains (hz j)) j η hj)

theorem tail_normalized_coordinate_density (ht : t.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    let U := (F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0).underlying
    let ε := FiniteRV.contractionOldLabelIndex F.tailContraction (Fin.natAdd 0 j)
    ∃ hε : ∀ u : U.obj.domain, u.val ε ≠ 0,
      coordinateDensityVolumeObject U ε hε = F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0 := by
  exact normalized_contraction_coordinate_density_eq_constant hc F.tailContraction
    (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property (Fin.natAdd 0 j) η (F.contains hη) hη0
    (fixed_rv_label_domain_retained_value (extendBase Y F.contains) z (fun j => F.contains (hz j)) j η hj)

end TwoOrderProductPreparations
end IntegrationInACVF.Section7
