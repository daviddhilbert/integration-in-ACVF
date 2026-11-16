module

public import Integration7.HKBasicGeneration
public import Integration7.HKBlowupUniversalProperty

@[expose] public section

/-! The single basic relation suffices to descend from actual graded
isomorphism classes to common-blowup classes, including weighted degree
zero and the genuine degree-one case, over any target semiring. -/
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7.HK
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {T : Type*} [Semiring T] (f : RVVolumeIsoSemiring hc C →+* T)
variable (hbasic : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
  f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))))

include hbasic in
theorem basic_volume_relation_respected (n : ℕ)
    (U V : RVVolumeObject (M := M) (C.base : Set M) n) (h : MuIsp (C.base : Set M) n U V) :
    f (volumeIsoSemiringClass hc C U) = f (volumeIsoSemiringClass hc C V) := by
  cases n with
  | zero =>
    apply congrArg f
    exact congrArg (DirectSum.of (RVVolumeIsoClasses hc C) 0) (Quotient.sound h)
  | succ k => exact common_blowup_image_eq_of_basic hc C f hbasic h

def basicVolumeBlowupDescend : RVVolumeBlowupSemiring hc C →+* T :=
  volumeBlowupUniversalDescend hc C f (basic_volume_relation_respected hc C f hbasic)

theorem basic_volume_blowup_descend_class {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    basicVolumeBlowupDescend hc C f hbasic
      (DirectSum.of (RVBlowupClasses hc C) n (rvVolumeBlowupClass hc C U)) =
      f (volumeIsoSemiringClass hc C U) :=
  volume_blowup_universal_descend_class hc C f (basic_volume_relation_respected hc C f hbasic) U

theorem basic_volume_blowup_descend_projection :
    (basicVolumeBlowupDescend hc C f hbasic).comp (rvVolumeGradedBlowupProjection hc C) = f :=
  volume_blowup_universal_descend_projection hc C f (basic_volume_relation_respected hc C f hbasic)

end IntegrationInACVF.Section7.HK
