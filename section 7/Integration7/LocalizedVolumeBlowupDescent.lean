module

public import Integration7.LocalizedBasicVolumeGeneration
public import Integration7.GradedVolumeBlowupProjection

@[expose] public section

/-! A semiring map identifying the basic pair and making the point a
unit descends uniquely through the actual geometric blowup quotient.
All common-blowup relations are proved to be respected. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {R : Type*} [Semiring R] (f : RVVolumeIsoSemiring hc C →+* R)
variable (hj : IsUnit (f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M)))))
variable (hBasic : f (volumeIsoSemiringClass hc C (n := 1) (degreeOnePointVolumeObject (C.base : Set M))) =
  f (volumeIsoSemiringClass hc C (n := 1) (degreeOneConeVolumeObject (C.base : Set M))))
include hj hBasic

theorem localized_muIsp_image_eq {n : ℕ}
    {U V : RVVolumeObject (M := M) (C.base : Set M) n} (h : MuIsp (C.base : Set M) n U V) :
    f (volumeIsoSemiringClass hc C U) = f (volumeIsoSemiringClass hc C V) := by
  cases n with
  | zero =>
    obtain ⟨e⟩ := h
    exact congrArg f (congrArg (DirectSum.of (RVVolumeIsoClasses hc C) 0)
      (Quotient.sound (s := rvVolumeIsoSetoid hc C 0) ⟨e⟩))
  | succ k => exact localized_common_volume_blowup_image_eq hc C f hj hBasic h

def localizedVolumeBlowupComponent (n : ℕ) : RVVolumeBlowupClasses hc C n →+ R where
  toFun := Quotient.lift (fun U => f (volumeIsoSemiringClass hc C U))
    (fun U V h => localized_muIsp_image_eq hc C f hj hBasic h)
  map_zero' := by
    change f (DirectSum.of (RVVolumeIsoClasses hc C) n 0) = 0
    rw [map_zero,map_zero]
  map_add' a b := by
    induction a using Quotient.inductionOn with
    | h U =>
      induction b using Quotient.inductionOn with
      | h V =>
        change f (DirectSum.of (RVVolumeIsoClasses hc C) n
          (rvVolumeIsoClass hc C U + rvVolumeIsoClass hc C V)) = _
        rw [map_add,map_add]
        rfl

def localizedVolumeBlowupDescend : RVVolumeBlowupSemiring hc C →+* R :=
  DirectSum.toSemiring (localizedVolumeBlowupComponent hc C f hj hBasic)
    (by change f 1 = 1; exact f.map_one)
    (by
      intro i j a b
      induction a using Quotient.inductionOn with
      | h U =>
        induction b using Quotient.inductionOn with
        | h V =>
          change f (DirectSum.of (RVVolumeIsoClasses hc C) (i+j)
            (rvVolumeIsoClassesProduct hc C i j (rvVolumeIsoClass hc C U) (rvVolumeIsoClass hc C V))) =
            f (DirectSum.of (RVVolumeIsoClasses hc C) i (rvVolumeIsoClass hc C U)) *
              f (DirectSum.of (RVVolumeIsoClasses hc C) j (rvVolumeIsoClass hc C V))
          rw [←map_mul,DirectSum.of_mul_of]
          rfl)

theorem localized_volume_blowup_descend_class {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    localizedVolumeBlowupDescend hc C f hj hBasic
      (DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupClass hc C U)) =
      f (volumeIsoSemiringClass hc C U) :=
  DirectSum.toSemiring_of _ _ _ n _

theorem localized_volume_blowup_descend_projection :
    (localizedVolumeBlowupDescend hc C f hj hBasic).comp (rvVolumeGradedBlowupProjection hc C) = f := by
  apply RingHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero]
  | add a b ha hb => rw [map_add,map_add,ha,hb]
  | of n a =>
    induction a using Quotient.inductionOn with
    | h U =>
      change localizedVolumeBlowupDescend hc C f hj hBasic
        (rvVolumeGradedBlowupProjection hc C (volumeIsoSemiringClass hc C U)) = _
      rw [volumeIsoSemiringClass,rvVolumeGradedBlowupProjection_of]
      exact localized_volume_blowup_descend_class hc C f hj hBasic U

theorem localized_volume_blowup_descend_unique
    (g : RVVolumeBlowupSemiring hc C →+* R)
    (hg : g.comp (rvVolumeGradedBlowupProjection hc C) = f) :
    g = localizedVolumeBlowupDescend hc C f hj hBasic := by
  apply RingHom.ext
  intro a
  obtain ⟨b,rfl⟩ := rvVolumeGradedBlowupProjection_surjective hc C a
  exact (RingHom.congr_fun hg b).trans
    (RingHom.congr_fun (localized_volume_blowup_descend_projection hc C f hj hBasic) b).symm

end IntegrationInACVF.Section7
