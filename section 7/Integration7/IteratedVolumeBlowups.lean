import Integration7.ElementaryBlowupConstruction
import Integration7.RVVolumeComposition
import Integration7.VolumeCoproductIsomorphism
import Integration7.RVVolumeInverse
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section9 SpecialTransformations.DefinableGeometry
noncomputable section
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure VolumeBlowup (U W : PositiveRVVolumeObject (M := M) S k) where
  locus : PositiveRVVolumeObject (M := M) S k
  complement : PositiveRVVolumeObject (M := M) S k
  blownLocus : PositiveRVVolumeObject (M := M) S k
  elementary : ElementaryBlowup locus blownLocus
  sourceIso : RVVolumeIso U (locus.coprod complement)
  targetIso : RVVolumeIso W (blownLocus.coprod complement)

inductive IteratedVolumeBlowup : ℕ →
    PositiveRVVolumeObject (M := M) S k → PositiveRVVolumeObject (M := M) S k → Prop where
  | refl (U) : IteratedVolumeBlowup 0 U U
  | step {n U V W} : Nonempty (VolumeBlowup U V) →
      IteratedVolumeBlowup n V W → IteratedVolumeBlowup (n+1) U W

namespace IteratedVolumeBlowup

theorem of_step {U V : PositiveRVVolumeObject (M := M) S k} (b : VolumeBlowup U V) :
    IteratedVolumeBlowup 1 U V := .step ⟨b⟩ (.refl V)

theorem trans {m n : ℕ} {U V W : PositiveRVVolumeObject (M := M) S k}
    (h : IteratedVolumeBlowup m U V) (g : IteratedVolumeBlowup n V W) :
    IteratedVolumeBlowup (m+n) U W := by
  induction h with
  | refl U => simpa only [Nat.zero_add] using g
  | step b h ih => simpa only [Nat.add_right_comm] using IteratedVolumeBlowup.step b (ih g)

end IteratedVolumeBlowup

def VolumeBlowupEquivalent (U V : PositiveRVVolumeObject (M := M) S k) : Prop :=
  ∃ m n U' V', IteratedVolumeBlowup m U U' ∧ IteratedVolumeBlowup n V V' ∧ Nonempty (RVVolumeIso U' V')

namespace VolumeBlowup
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {U U' W W' : PositiveRVVolumeObject (M := M) (C.base : Set M) k}

def on_coprod {A B : PositiveRVVolumeObject (M := M) (C.base : Set M) k}
    (b : ElementaryBlowup A B) (R : PositiveRVVolumeObject (M := M) (C.base : Set M) k) :
    VolumeBlowup (A.coprod R) (B.coprod R) where
  locus := A
  complement := R
  blownLocus := B
  elementary := b
  sourceIso := RVVolumeIso.refl hc C _
  targetIso := RVVolumeIso.refl hc C _

def transport (b : VolumeBlowup U W) (f : RVVolumeIso U' U) (g : RVVolumeIso W' W) :
    VolumeBlowup U' W' where
  locus := b.locus
  complement := b.complement
  blownLocus := b.blownLocus
  elementary := b.elementary
  sourceIso := f.trans hc C b.sourceIso
  targetIso := g.trans hc C b.targetIso

end VolumeBlowup

namespace VolumeBlowupEquivalent
variable (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
variable {U V : PositiveRVVolumeObject (M := M) (C.base : Set M) k}

theorem of_iso (f : RVVolumeIso U V) : VolumeBlowupEquivalent U V :=
  ⟨0, 0, U, V, .refl U, .refl V, ⟨f⟩⟩

include hc

theorem refl (U : PositiveRVVolumeObject (M := M) (C.base : Set M) k) : VolumeBlowupEquivalent U U :=
  of_iso C (RVVolumeIso.refl hc C U)

theorem symm (h : VolumeBlowupEquivalent U V) : VolumeBlowupEquivalent V U := by
  obtain ⟨m, n, U', V', hU, hV, ⟨e⟩⟩ := h
  exact ⟨n, m, V', U', hV, hU, ⟨e.symm hc C⟩⟩

theorem of_blowup (b : VolumeBlowup U V) : VolumeBlowupEquivalent U V :=
  ⟨1, 0, V, V, IteratedVolumeBlowup.of_step b, .refl V, ⟨RVVolumeIso.refl hc C V⟩⟩

end VolumeBlowupEquivalent
end IntegrationInACVF.Section7
