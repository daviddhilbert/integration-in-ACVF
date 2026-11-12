import IntegrationSection6.RawSelectedContractions
import IntegrationSection6.GammaSwappedVolumes
import IntegrationSection6.GammaVolumeSliceEmbeddings
import IntegrationSection6.RawContractionDomain

/-! A slice of the raw selected contraction has precisely the final
contraction labels with the selected original labels fixed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a k : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
variable (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
variable (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
  {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
variable (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)

theorem gammaRawSelectedPrepend_value (u : rvObjectDomain C.contractionObject) :
    gammaVolumeValue (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC)).toGammaRVObject u =
      Fin.append (u.val ∘ (fun j => suffixIndex C.program.rvArity_le (ρ j))) (u.val ∘ C.volumeIndex) := by
  change Fin.append (u.val ∘ C.volumeIndex) (u.val ∘ (fun j => suffixIndex C.program.rvArity_le (ρ j))) ∘
    (@finAddFlip k n) = _
  exact append_finAddFlip _ _

theorem rawSelectedSlice_mem (t : Fin k → RV (M := M))
    (P : GammaFiniteGraphPresentation ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩ C.arity n
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC))).rowDomain (fun j => (t j).val))
      ((gammaVolumeSliceSchema (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC))).rowVolume (fun j => (t j).val)))
    (r : Fin C.arity → RV (M := M)) :
    r ∈ carrier P.domain ↔ (Fin.elim0,r) ∈ carrier C.target ∧
      r ∘ (fun j => suffixIndex C.program.rvArity_le (ρ j)) = t := by
  refine (volumeSlicePresentation_mem
    (gammaSwapVolumeBlocks (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC)) t P r).trans ?_
  constructor
  · rintro ⟨u,hu,ht⟩
    have hpre := gammaRawSelectedPrepend_value hκ hs hreal hBS hU ρ hfin C hC u
    have hv : u.val ∘ (fun j => suffixIndex C.program.rvArity_le (ρ j)) = t := by
      funext j
      have h := congrFun ht j
      rw [Function.comp_apply,hpre,Fin.append_left] at h
      exact h
    exact ⟨(rawContractionDomain_iff C (Fin.elim0,r)).mp (hu ▸ u.property),hu ▸ hv⟩
  · rintro ⟨hr,ht⟩
    let u : rvObjectDomain C.contractionObject := ⟨r,(rawContractionDomain_iff C (Fin.elim0,r)).mpr hr⟩
    refine ⟨u,rfl,?_⟩
    rw [gammaRawSelectedPrepend_value]
    exact (funext fun j => Fin.append_left _ _ j).trans ht

end IntegrationInACVF.Section6.FiniteRV
