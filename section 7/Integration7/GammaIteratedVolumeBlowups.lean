module

public import Integration7.GammaVolumeIsomorphismClasses
public import Integration7.GammaChartedVolumeBlowups

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Finite chains of the actual volume blowups, retaining full original
Gamma data at every step. Forgetting this data gives the existing chain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

inductive GammaIteratedVolumeBlowup (B : Base (M := M)) (S : Set M) (k : ℕ) :
    ℕ → GammaVolumeObjects B S k → GammaVolumeObjects B S k → Prop where
  | refl (U) : GammaIteratedVolumeBlowup B S k 0 U U
  | step {n U V W} : (∃ b : VolumeBlowup U.val V.val, b.GammaDefinable B) →
      GammaIteratedVolumeBlowup B S k n V W → GammaIteratedVolumeBlowup B S k (n+1) U W

variable {B : Base (M := M)} {S : Set M} {k m n : ℕ}
variable {U V W : GammaVolumeObjects B S k}

theorem GammaIteratedVolumeBlowup.toOrdinary
    (h : GammaIteratedVolumeBlowup B S k n U V) : IteratedVolumeBlowup n U.val V.val := by
  induction h with
  | refl U => exact .refl U.val
  | step b rest ih => exact .step ⟨b.choose⟩ ih

theorem GammaIteratedVolumeBlowup.trans
    (h : GammaIteratedVolumeBlowup B S k m U V) (g : GammaIteratedVolumeBlowup B S k n V W) :
    GammaIteratedVolumeBlowup B S k (m+n) U W := by
  induction h with
  | refl U => simpa only [Nat.zero_add] using g
  | step b rest ih => simpa only [Nat.add_right_comm] using GammaIteratedVolumeBlowup.step b (ih g)

theorem GammaIteratedVolumeBlowup.transport_source
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {U U' W : GammaVolumeObjects B (C.base : Set M) k}
    (h : GammaIteratedVolumeBlowup B (C.base : Set M) k n U W)
    (f : RVVolumeIso U'.val U.val) (hf : f.GammaDefinable B) :
    ∃ W', GammaIteratedVolumeBlowup B (C.base : Set M) k n U' W' ∧
      ∃ e : RVVolumeIso W'.val W.val, e.GammaDefinable B := by
  cases h with
  | refl U => exact ⟨U',.refl U',f,hf⟩
  | @step n U V W b rest =>
    obtain ⟨b,hb⟩ := b
    let g := RVVolumeIso.refl hc C V.val
    let b' := b.transport hc C f g
    have hb' : b'.GammaDefinable B := hb.transport hc C f g hf (V.property.identity_iso hc C)
    exact ⟨W,.step ⟨b',hb'⟩ rest,RVVolumeIso.refl hc C W.val,W.property.identity_iso hc C⟩

end IntegrationInACVF.Section7
