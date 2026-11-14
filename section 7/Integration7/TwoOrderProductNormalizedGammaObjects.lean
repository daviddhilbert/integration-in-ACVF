import Integration7.TwoOrderProductCoordinateDensities
import Integration7.NormalizedContractionCoordinateGraphs

/-! The retained density labels give actual original-Gamma volume
objects for both normalized product contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5

namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk P.real < κ)
variable (hc : CanonicalStructure.IsCanonical (M := M)) (F : TwoOrderProductPreparations X Y D E r t z hz P)

theorem head_normalized_volume_gamma (hPS : P.real ⊆ S) (hr : r.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    VolumeObjectGamma (F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0) P := by
  obtain ⟨hδ,hEq⟩ := F.head_normalized_coordinate_density hκ hs hsmall hc hr η hη hη0 j hj
  have hG := normalized_coordinate_density_volume_gamma hc F.headContraction
    (F.headRawFiniteRVObject hκ hs hsmall hc hr).property (hPS.trans F.contains)
    (gamma_headImage F.headPreparation.target
      (GammaChainDefinable.target P F.headPreparation.special.chain F.headPreparation.gamma)) _ hδ
  exact Eq.mp (congrArg (fun U => VolumeObjectGamma U P) hEq) hG

theorem tail_normalized_volume_gamma (hPS : P.real ⊆ S) (ht : t.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    VolumeObjectGamma (F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0) P := by
  obtain ⟨hδ,hEq⟩ := F.tail_normalized_coordinate_density hκ hs hsmall hc ht η hη hη0 j hj
  have hG := normalized_coordinate_density_volume_gamma hc F.tailContraction
    (F.tailRawFiniteRVObject hκ hs hsmall hc ht).property (hPS.trans F.contains)
    (gamma_headImage F.tailPreparation.target
      (GammaChainDefinable.target P F.tailPreparation.special.chain F.tailPreparation.gamma)) _ hδ
  exact Eq.mp (congrArg (fun U => VolumeObjectGamma U P) hEq) hG

def headNormalizedGammaObject (hPS : P.real ⊆ S) (hr : r.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    GammaVolumeObjects P F.codes 1 :=
  ⟨F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0,
    F.head_normalized_volume_gamma hκ hs hsmall hc hPS hr η hη hη0 j hj⟩

def tailNormalizedGammaObject (hPS : P.real ⊆ S) (ht : t.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) (j : Fin d) (hj : z j = η) :
    GammaVolumeObjects P F.codes 1 :=
  ⟨F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0,
    F.tail_normalized_volume_gamma hκ hs hsmall hc hPS ht η hη hη0 j hj⟩

end IntegrationInACVF.Section7.TwoOrderProductPreparations
