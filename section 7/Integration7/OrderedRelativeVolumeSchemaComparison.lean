import Integration7.HeadTailVolumeSelectors
import Integration7.GlobalRelativeVolumeContractions
import Integration7.OrderedAppendVolumeFiniteness
import Integration7.SelectedVolumeDegreeTransport
import Integration7.GenericRelativeHeadVolumeComparison
import Integration7.GenericOrderedAppendVolumeContractions
import Integration7.RelativeHeadVolumeComparison
import Integration7.OrderedAppendVolumeContractions

/-! Original global measure preservation is sufficient for comparison
of any specified head-first ordered contractions. Exceptional frozen
fibres are handled through the generic selected-volume induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6

namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a b l r : ℕ}

set_option maxHeartbeats 2400000 in
theorem ordered_relative_volume_schema_comparison {κ : Cardinal}
    (hc : CanonicalStructure.IsCanonical (M := M)) (C : BaseContext M)
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hreal : Cardinal.mk B.real < κ) (hgamma : Cardinal.mk B.gamma < κ)
    (γ : Values.Gamma (M := M)) (hγ : γ ∈ B.gamma) (hγ1 : 1 < γ)
    (hBC : B.real ⊆ (C.base : Set M)) (hBase : B.real = (C.base : Set M))
    (U : DefSet (M := M) (C.base : Set M) (n+1) a) (V : DefSet (M := M) (C.base : Set M) (n+1) b)
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (hfinU : ∀ x : Fin (n+1) → VF (M := M), {s : Fin a → RV (M := M) | (x,s) ∈ carrier U}.Finite)
    (hfinV : ∀ x : Fin (n+1) → VF (M := M), {s : Fin b → RV (M := M) | (x,s) ∈ carrier V}.Finite)
    (f : Map U V) (hf : Function.Bijective f) (hfΓ : GammaGraphDefinable B (pointMapGraph f))
    (hi : UnaryRelative f 0)
    (ω : VolumeForm (rawSpecialSet hc U)) (π : VolumeForm (rawSpecialSet hc V))
    (δ : Fin a) (ε : Fin b)
    (hω : ∀ q, ω.value q = q.val.2 δ) (hπ : ∀ q, π.value q = q.val.2 ε)
    (hm : PreservesVFVolume ω π (rawSpecialMap hc f))
    {U₀ : DefSet (M := M) (C.base : Set M) 0 l} {V₀ : DefSet (M := M) (C.base : Set M) 0 r}
    (P : OrderedContractionProgram (C.base : Set M) U U₀)
    (Q : OrderedContractionProgram (C.base : Set M) V V₀)
    (hP : GammaProgramDefinable B P) (hQ : GammaProgramDefinable B Q) :
    (gammaSelectedVolumeSchema U₀ (gamma_program_final_set P hP) P.volumeIndex
      (suffixIndex P.rvArity_le δ)).commonByGammaGeometry
    (gammaSelectedVolumeSchema V₀ (gamma_program_final_set Q hQ) Q.volumeIndex
      (suffixIndex Q.rvArity_le ε)) (fun j : Fin 0 => (Fin.elim0 j : VF (M := M)).val) := by
  have hδ : ∀ p ∈ carrier U, (p.2 δ).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => ω.nonzero ⟨p,hp⟩ ((hω ⟨p,hp⟩).trans h))
  have hε : ∀ p ∈ carrier V, (p.2 ε).val ≠ iRVZero := fun p hp =>
    (rv_nonzero_iff_raw _).mp (fun h => π.nonzero ⟨p,hp⟩ ((hπ ⟨p,hp⟩).trans h))
  cases P with
  | step T tail =>
    cases Q with
    | step E etail =>
      have h := ordered_relative_volume_comparison hc C hκ hs hreal hgamma γ hγ hγ1 hBC hBase
        U V hU hV hfinU hfinV f hf hfΓ hi ω π δ ε hω hπ hm T E
        hP.1 hQ.1 hP.2.1 hQ.2.1 tail etail hP.2.2 hQ.2.2 (Fin.elim0 : Fin 0 → VF (M := M))
      have hδ' := ordered_append_retained_density_nonzero (OrderedContractionProgram.step T tail) δ hδ
      have hε' := ordered_append_retained_density_nonzero (OrderedContractionProgram.step E etail) ε hε
      rw [ordered_append_density_index] at hδ' hε'
      rw [head_tail_append_density_index,head_tail_append_density_index] at h
      apply selected_volume_geometry_reindex (head_tail_volume_degree n)
        U₀ V₀ (gamma_program_final_set (OrderedContractionProgram.step T tail) hP) (gamma_program_final_set (OrderedContractionProgram.step E etail) hQ)
        (orderedAppendVolumeIndex (k := 0) tail (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a)))
        (orderedAppendVolumeIndex (k := 0) etail (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b)))
        (OrderedContractionProgram.step T tail).volumeIndex (OrderedContractionProgram.step E etail).volumeIndex ?_ ?_
        (suffixIndex (OrderedContractionProgram.step T tail).rvArity_le δ) (suffixIndex (OrderedContractionProgram.step E etail).rvArity_le ε)
        hδ' hε' (Fin.elim0 : Fin 0 → VF (M := M)) h
      · funext i
        have hi : (finCongr (congrArg Nat.succ (head_tail_volume_degree n))).symm i =
            Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i := Fin.ext rfl
        exact (congrArg (orderedAppendVolumeIndex (k := 0) tail
          (headVolumeIndex T (Fin.elim0 : Fin 0 → Fin a))) hi).trans
          (head_tail_append_volume_index T tail i)
      · funext i
        have hi : (finCongr (congrArg Nat.succ (head_tail_volume_degree n))).symm i =
            Fin.cast (congrArg Nat.succ (head_tail_volume_degree n)).symm i := Fin.ext rfl
        exact (congrArg (orderedAppendVolumeIndex (k := 0) etail
          (headVolumeIndex E (Fin.elim0 : Fin 0 → Fin b))) hi).trans
          (head_tail_append_volume_index E etail i)

end IntegrationInACVF.Section7
