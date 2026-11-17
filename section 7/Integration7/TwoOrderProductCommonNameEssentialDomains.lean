module

public import Integration7.TwoOrderProductCommonNameGeometry
public import Integration7.TwoOrderProductNormalization

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Fixed-name presentations keep the actual final contraction domains
and volume coordinate selectors in both VF orders. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

open SpecialTransformations.Section9
namespace IntegrationInACVF.Section7.TwoOrderProductPreparations
set_option allowUnsafeReducibility true in
attribute [local reducible] PositiveRVVolumeObject.essential
  SpecialTransformations.Section9.rvFiniteEssential SpecialTransformations.Section9.rvEssential
  SpecialTransformations.Section4.RVObject.restrict headNormalizedVolumeObject tailNormalizedVolumeObject
  normalizedUnitVolumeContraction canonicalNormalizedFiniteContraction canonicalRVObject
  PositiveRVVolumeObject.rescale

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {P : Base (M := M)} {S R : Set M} {d : ℕ}
variable {X Y : DefSet (M := M) S 2 0} {D E : DefSet (M := M) S 1 0}
variable {r t : RV (M := M)} {z : Fin d → RV (M := M)} {hz : ∀ j, (z j).val ∈ S}
variable (F : TwoOrderProductPreparations X Y D E r t z hz P)
variable (hSR : S ⊆ R) (hNames : commonRealNames P ⊆ R)

variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : SpecialTransformations.Section3.Saturated M κ)
variable (hsmall : Cardinal.mk P.real < κ) (hc : CanonicalStructure.IsCanonical (M := M))

theorem head_present_essential_domain (hr : r.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let G := F.present hSR hNames
    let U := G.headNormalizedVolumeObject hκ hs hsmall hc (hSR hr) η (hSR hη) hη0
    let V := F.headNormalizedVolumeObject hκ hs hsmall hc hr η hη hη0
    U.essential.obj.domain.carrier = V.essential.obj.domain.carrier := by
  intro G U V
  have hD : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier :=
    F.head_present_normalized_domain hSR hNames
  ext x
  constructor
  · intro hx
    have hxD := rvEssentialLabels_subset U.underlying.obj hx
    let v : V.underlying.obj.domain := ⟨x,(Set.ext_iff.mp hD x).mp hxD⟩
    exact (mem_rvEssentialLabels V.underlying.obj v).mpr (fun i => U.essential_nonzero ⟨x,hx⟩ i)
  · intro hx
    have hxD := rvEssentialLabels_subset V.underlying.obj hx
    let u : U.underlying.obj.domain := ⟨x,(Set.ext_iff.mp hD x).mpr hxD⟩
    exact (mem_rvEssentialLabels U.underlying.obj u).mpr (fun i => V.essential_nonzero ⟨x,hx⟩ i)

theorem tail_present_essential_domain (ht : t.val ∈ S)
    (η : RV (M := M)) (hη : η.val ∈ S) (hη0 : η ≠ 0) :
    let G := F.present hSR hNames
    let U := G.tailNormalizedVolumeObject hκ hs hsmall hc (hSR ht) η (hSR hη) hη0
    let V := F.tailNormalizedVolumeObject hκ hs hsmall hc ht η hη hη0
    U.essential.obj.domain.carrier = V.essential.obj.domain.carrier := by
  intro G U V
  have hD : U.underlying.obj.domain.carrier = V.underlying.obj.domain.carrier :=
    F.tail_present_normalized_domain hSR hNames
  ext x
  constructor
  · intro hx
    have hxD := rvEssentialLabels_subset U.underlying.obj hx
    let v : V.underlying.obj.domain := ⟨x,(Set.ext_iff.mp hD x).mp hxD⟩
    exact (mem_rvEssentialLabels V.underlying.obj v).mpr (fun i => U.essential_nonzero ⟨x,hx⟩ i)
  · intro hx
    have hxD := rvEssentialLabels_subset V.underlying.obj hx
    let u : U.underlying.obj.domain := ⟨x,(Set.ext_iff.mp hD x).mpr hxD⟩
    exact (mem_rvEssentialLabels U.underlying.obj u).mpr (fun i => V.essential_nonzero ⟨x,hx⟩ i)

end IntegrationInACVF.Section7.TwoOrderProductPreparations
