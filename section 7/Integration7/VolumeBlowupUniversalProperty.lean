import Integration7.PositiveElementaryBasicGeneration

/-! The universal property of the actual common-blowup semiring.
A map descends exactly when it respects the genuine fixed-degree
geometric relations; no basic-relation generation claim is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {R : Type*} [Semiring R] (f : RVVolumeIsoSemiring hc C →+* R)
variable (hrel : ∀ n (U V : RVVolumeObject (M := M) (C.base : Set M) n),
  MuIsp (C.base : Set M) n U V →
    f (volumeIsoSemiringClass hc C U)=f (volumeIsoSemiringClass hc C V))
include hrel

def volumeBlowupUniversalComponent (n : ℕ) : RVVolumeBlowupClasses hc C n →+ R where
  toFun := Quotient.lift (fun U => f (volumeIsoSemiringClass hc C U))
    (fun U V h => hrel n U V h)
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

def volumeBlowupUniversalDescend : RVVolumeBlowupSemiring hc C →+* R :=
  DirectSum.toSemiring (volumeBlowupUniversalComponent hc C f hrel)
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

theorem volume_blowup_universal_descend_class {n : ℕ}
    (U : RVVolumeObject (M := M) (C.base : Set M) n) :
    volumeBlowupUniversalDescend hc C f hrel
      (DirectSum.of (RVVolumeBlowupClasses hc C) n (rvVolumeBlowupClass hc C U)) =
      f (volumeIsoSemiringClass hc C U) :=
  DirectSum.toSemiring_of _ _ _ n _

theorem volume_blowup_universal_descend_projection :
    (volumeBlowupUniversalDescend hc C f hrel).comp (rvVolumeGradedBlowupProjection hc C) = f := by
  apply RingHom.ext
  intro a
  induction a using DirectSum.induction_on with
  | zero => rw [map_zero,map_zero]
  | add a b ha hb => rw [map_add,map_add,ha,hb]
  | of n a =>
    induction a using Quotient.inductionOn with
    | h U =>
      change volumeBlowupUniversalDescend hc C f hrel
        (rvVolumeGradedBlowupProjection hc C (volumeIsoSemiringClass hc C U)) = _
      rw [volumeIsoSemiringClass,rvVolumeGradedBlowupProjection_of]
      exact volume_blowup_universal_descend_class hc C f hrel U

theorem volume_blowup_universal_descend_unique
    (g : RVVolumeBlowupSemiring hc C →+* R)
    (hg : g.comp (rvVolumeGradedBlowupProjection hc C) = f) :
    g = volumeBlowupUniversalDescend hc C f hrel := by
  apply RingHom.ext
  intro a
  obtain ⟨b,rfl⟩ := rvVolumeGradedBlowupProjection_surjective hc C a
  exact (RingHom.congr_fun hg b).trans
    (RingHom.congr_fun (volume_blowup_universal_descend_projection hc C f hrel) b).symm

end IntegrationInACVF.Section7
