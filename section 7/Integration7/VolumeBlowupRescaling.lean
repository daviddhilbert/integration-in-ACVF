import Integration7.VolumeDensityRescaling
import Integration7.VolumeBlowupEquivalence
import Integration7.VolumeCoproductAssociativity

/-! Multiplying all densities by the same named nonzero constant
preserves actual elementary blowups and their common-refinement relation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}
local notation "RV" => CanonicalRV.RVSort M

def ElementaryBlowup.rescale {U V : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U V) (c : RV) (hc : c.val ∈ S) (h0 : c ≠ 0) :
    ElementaryBlowup (U.rescale c hc h0) (V.rescale c hc h0) where
  admissible := ⟨b.admissible.nonzero,b.admissible.algebraic⟩
  chartMap := b.chartMap
  chartMap_bijective := b.chartMap_bijective
  head := b.head
  last := b.last
  volume x := congrArg (fun t => c * t) (b.volume x)

def volumeRescaleCoprodIso
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k)
    (c : RV) (hC : c.val ∈ C.base) (h0 : c ≠ 0) :
    RVVolumeIso ((U.coprod V).rescale c hC h0)
      ((U.rescale c hC h0).coprod (V.rescale c hC h0)) := by
  apply RVVolumeIso.of_preserving_coordinates_full hc C
    (U := (U.coprod V).rescale c hC h0)
    (V := (U.rescale c hC h0).coprod (V.rescale c hC h0))
    (Iso.refl (U.coprod V).underlying)
  · intro x
    rfl
  · intro x
    rcases volumeCoprod_cases U V x with ⟨u,rfl⟩ | ⟨v,rfl⟩
    · exact (coprod_density_left (U.rescale c hC h0) (V.rescale c hC h0) u).trans
        (congrArg (fun t => c * t) (coprod_density_left U V u)).symm
    · exact (coprod_density_right (U.rescale c hC h0) (V.rescale c hC h0) v).trans
        (congrArg (fun t => c * t) (coprod_density_right U V v)).symm

def VolumeBlowup.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : VolumeBlowup U V) (c : RV) (hC : c.val ∈ C.base) (h0 : c ≠ 0) :
    VolumeBlowup (U.rescale c hC h0) (V.rescale c hC h0) where
  locus := b.locus.rescale c hC h0
  complement := b.complement.rescale c hC h0
  blownLocus := b.blownLocus.rescale c hC h0
  elementary := b.elementary.rescale c hC h0
  sourceIso := (b.sourceIso.rescale c hC h0).trans hc C
    (volumeRescaleCoprodIso hc C b.locus b.complement c hC h0)
  targetIso := (b.targetIso.rescale c hC h0).trans hc C
    (volumeRescaleCoprodIso hc C b.blownLocus b.complement c hC h0)

theorem IteratedVolumeBlowup.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k} {d : ℕ}
    (h : IteratedVolumeBlowup d U V) (c : RV) (hC : c.val ∈ C.base) (h0 : c ≠ 0) :
    IteratedVolumeBlowup d (U.rescale c hC h0) (V.rescale c hC h0) := by
  induction h with
  | refl U => exact .refl _
  | step b h ih => exact .step ⟨b.some.rescale hc C c hC h0⟩ ih

theorem VolumeBlowupEquivalent.rescale
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (h : VolumeBlowupEquivalent U V) (c : RV) (hC : c.val ∈ C.base) (h0 : c ≠ 0) :
    VolumeBlowupEquivalent (U.rescale c hC h0) (V.rescale c hC h0) := by
  obtain ⟨a,b,U',V',hU,hV,⟨e⟩⟩ := h
  exact ⟨a,b,U'.rescale c hC h0,V'.rescale c hC h0,
    hU.rescale hc C c hC h0,hV.rescale hc C c hC h0,⟨e.rescale c hC h0⟩⟩

end IntegrationInACVF.Section7
