module

public import Integration7.VFVolumeBijections
public import Section9.SpecialJacobianAE

@[expose] public section

/-! Actual special bijections, in both directions, preserve any retained
density. The exceptional sets come from the checked determinant-one theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

theorem special_vf_jacobian_one
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n a b : ℕ} (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (T : SpecialTransformations.Section5.SpecialBijection A B) :
    VFAlmostEverywhere (rawSpecialSet hc A)
        (fun p => HasMixedVFJacobianAt (rawSpecialMap hc T.toMap) p 1) ∧
      VFAlmostEverywhere (rawSpecialSet hc B)
        (fun p => HasMixedVFJacobianAt (rawSpecialMap hc T.inverseMap) p 1) := by
  letI : CharZero (VFType (M := M)) := Section6.vfCharZero_of_model00 C.model00
  obtain ⟨E, D, hE, hD, hdE, hdD, hf, hg⟩ :=
    lemma_9_11_ae hc C.uncountable.le C.saturated C.small hn T
  exact ⟨⟨E, hE, hdE, hf⟩, ⟨D, hD, hdD, hg⟩⟩

theorem special_preserves_volume
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    {n a b : ℕ} (hn : 0 < n)
    {A : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n a}
    {B : SpecialTransformations.Section5.DefSet (M := M) (C.base : Set M) n b}
    (T : SpecialTransformations.Section5.SpecialBijection A B)
    (ω : VolumeForm (rawSpecialSet hc A)) (π : VolumeForm (rawSpecialSet hc B))
    (hω : ∀ p, ω.value p = π.value ((rawSpecialMap hc T.toMap) p)) :
    PreservesVFVolume ω π (rawSpecialMap hc T.toMap) ∧
      PreservesVFVolume π ω (rawSpecialMap hc T.inverseMap) := by
  obtain ⟨hf, hg⟩ := special_vf_jacobian_one hc C hn T
  constructor
  · apply hf.mono
    intro p hJ
    exact ⟨1, hJ, by rw [RVOperations.rv_one, mul_one]; exact hω p⟩
  · apply hg.mono
    intro p hJ
    refine ⟨1, hJ, ?_⟩
    rw [RVOperations.rv_one, mul_one]
    have h := hω ((rawSpecialMap hc T.inverseMap) p)
    have he : (rawSpecialMap hc T.toMap) ((rawSpecialMap hc T.inverseMap) p) = p :=
      T.apply_inverse p
    rw [he] at h
    exact h.symm

end IntegrationInACVF.Section7
