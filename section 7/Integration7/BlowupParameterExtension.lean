import Integration7.VolumeIsoParameterExtension
import Integration7.IteratedVolumeBlowups

/-! Parameter enlargement preserves actual elementary charts and finite
common forward blowups, including their exact lengths and densities. -/

set_option backward.isDefEq.respectTransparency false
noncomputable section
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {S T : Set M} {k : ℕ}

theorem BlowupAdmissible.extend {U : PositiveRVVolumeObject (M := M) S k}
    (h : BlowupAdmissible U) (hST : S ⊆ T) : BlowupAdmissible (U.extend hST) where
  nonzero := h.nonzero
  algebraic u := (h.algebraic ⟨u.val,u.property⟩).mono (by
    rintro x (hx | hx)
    · exact Or.inl (hST hx)
    · exact Or.inr hx)

def ElementaryBlowup.extend {U V : PositiveRVVolumeObject (M := M) S k}
    (b : ElementaryBlowup U V) (hST : S ⊆ T) : ElementaryBlowup (U.extend hST) (V.extend hST) where
  admissible := b.admissible.extend hST
  chartMap := b.chartMap.extend hST
  chartMap_bijective := b.chartMap_bijective
  head := b.head
  last := b.last
  volume := b.volume

def VolumeBlowup.extend {U V : PositiveRVVolumeObject (M := M) S k}
    (b : VolumeBlowup U V) (hST : S ⊆ T) : VolumeBlowup (U.extend hST) (V.extend hST) where
  locus := b.locus.extend hST
  complement := b.complement.extend hST
  blownLocus := b.blownLocus.extend hST
  elementary := b.elementary.extend hST
  sourceIso := b.sourceIso.extend hST
  targetIso := b.targetIso.extend hST

theorem IteratedVolumeBlowup.extend {U V : PositiveRVVolumeObject (M := M) S k}
    {n : ℕ} (b : IteratedVolumeBlowup n U V) (hST : S ⊆ T) :
    IteratedVolumeBlowup n (U.extend hST) (V.extend hST) := by
  induction b with
  | refl U => exact .refl (U.extend hST)
  | step b rest ih => exact .step (b.map (fun b => b.extend hST)) ih

theorem VolumeBlowupEquivalent.extend {U V : PositiveRVVolumeObject (M := M) S k}
    (b : VolumeBlowupEquivalent U V) (hST : S ⊆ T) :
    VolumeBlowupEquivalent (U.extend hST) (V.extend hST) := by
  obtain ⟨m,n,U',V',hU,hV,⟨e⟩⟩ := b
  exact ⟨m,n,U'.extend hST,V'.extend hST,hU.extend hST,hV.extend hST,⟨e.extend hST⟩⟩

end IntegrationInACVF.Section7
