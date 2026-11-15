import Integration7.VolumeDensityRescaling
import Integration7.VFVolumeIsomorphisms

/-! Named nonzero density rescaling on genuine VF volume objects and
almost-everywhere volume isomorphisms, retaining their actual maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def PositiveVFVolumeObject.rescale (U : PositiveVFVolumeObject (M := M) S k)
    (c : CanonicalRV.RVSort M) (hc : c.val ∈ S) (h0 : c ≠ 0) :
    PositiveVFVolumeObject (M := M) S k where
  arity := U.arity
  domain := U.domain
  finite_labels := U.finite_labels
  form := U.form.rescale c hc h0

def VFVolumeBijection.rescale {U V : PositiveVFVolumeObject (M := M) S k}
    (f : VFVolumeBijection U V) (c : CanonicalRV.RVSort M) (hc : c.val ∈ S) (h0 : c ≠ 0) :
    VFVolumeBijection (U.rescale c hc h0) (V.rescale c hc h0) where
  map := f.map
  bijective := f.bijective
  preserves := f.preserves.mono (by
    rintro p ⟨J,hJ,hω⟩
    refine ⟨J,hJ,?_⟩
    change c * U.form.value p=(c * V.form.value (f.map p)) * CanonicalRV.encodedRv J
    rw [hω,mul_assoc])

def VFVolumeIso.rescale {U V : PositiveVFVolumeObject (M := M) S k}
    (f : VFVolumeIso U V) (c : CanonicalRV.RVSort M) (hc : c.val ∈ S) (h0 : c ≠ 0) :
    VFVolumeIso (U.rescale c hc h0) (V.rescale c hc h0) where
  source := f.source
  target := f.target
  source_subset := f.source_subset
  target_subset := f.target_subset
  source_complement_small := f.source_complement_small
  target_complement_small := f.target_complement_small
  bijection := {
    map := f.bijection.map
    bijective := f.bijection.bijective
    preserves := f.bijection.preserves.mono (by
      rintro p ⟨J,hJ,hω⟩
      refine ⟨J,hJ,?_⟩
      change c * (U.restrict f.source f.source_subset).form.value p=
        (c * (V.restrict f.target f.target_subset).form.value (f.bijection.map p)) * CanonicalRV.encodedRv J
      rw [hω,mul_assoc]) }
end IntegrationInACVF.Section7
