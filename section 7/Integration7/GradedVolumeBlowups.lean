import Integration7.IteratedVolumeBlowups
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

def MuIsp (S : Set M) : (n : ℕ) → RVVolumeObject (M := M) S n → RVVolumeObject (M := M) S n → Prop
  | 0, U, V => Nonempty ((show RVFiniteObject (M := M) S 0 from U) ≅
      (show RVFiniteObject (M := M) S 0 from V))
  | _+1, U, V => VolumeBlowupEquivalent U V

@[simp] theorem muIsp_zero_iff (S : Set M) (U V : RVFiniteObject (M := M) S 0) :
    MuIsp S 0 U V ↔ Nonempty (U ≅ V) := Iff.rfl

@[simp] theorem muIsp_succ_iff (S : Set M) (k : ℕ) (U V : RVVolumeObject (M := M) S (k+1)) :
    MuIsp S (k+1) U V ↔ VolumeBlowupEquivalent U V := Iff.rfl

theorem muIsp_refl (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} (U : RVVolumeObject (M := M) (C.base : Set M) n) : MuIsp (C.base : Set M) n U U := by
  cases n with
  | zero => exact ⟨Iso.refl (show RVFiniteObject (M := M) (C.base : Set M) 0 from U)⟩
  | succ k => exact VolumeBlowupEquivalent.refl hc C U

theorem muIsp_symm (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n : ℕ} {U V : RVVolumeObject (M := M) (C.base : Set M) n}
    (h : MuIsp (C.base : Set M) n U V) : MuIsp (C.base : Set M) n V U := by
  cases n with
  | zero => obtain ⟨e⟩ := h; exact ⟨e.symm⟩
  | succ k => exact VolumeBlowupEquivalent.symm hc C h
end IntegrationInACVF.Section7
