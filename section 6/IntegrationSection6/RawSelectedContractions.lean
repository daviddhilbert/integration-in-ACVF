import IntegrationSection6.GammaRawStandardContractions
import IntegrationSection6.RawSelectedNormalizationValues
import IntegrationSection6.FiniteGammaIsoLaws

/-! Actual finite contraction objects before first-volume normalization.
The full volume tuple, including selected original labels, is preserved. -/
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
local notation "N" => (@CanonicalStructure.normalize M sM)

def gammaRawSelectedContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVFiniteObject B (n+k) where
  toGammaRVObject := gammaAppendSelectedVolume
    (gammaRawContractionObject C hBS (gamma_program_final_set C.program hC))
    (fun j => suffixIndex C.program.rvArity_le (ρ j))
  finite_volume := by
    let Q := gammaFiniteSelectedContraction hκ hs hreal hBS hU ρ hfin C hC
    intro t
    apply (Q.finite_volume t).of_injOn (f := toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex)
    · intro u hu
      apply Subtype.ext
      exact (rawSelectedNormalization_volume C ρ u).trans (congrArg Subtype.val hu)
    · intro u hu v hv he
      exact (toFirstVolume_bijective _ _).1 he

def gammaRawSelectedNormalizationIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVIso (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC).toGammaRVObject
      (gammaFiniteSelectedContraction hκ hs hreal hBS hU ρ hfin C hC).toGammaRVObject := by
  let F := toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex
  apply gammaIsoOfFiniteEquiv _ _ (Equiv.ofBijective F (toFirstVolume_bijective _ _))
  · apply gamma_rv_graph_of_global_formula F
      (@rawRVProjectionMap M sM hM B.real C.arity (n+C.arity)
        (prependVolumeIndex C.volumeIndex) (PresentedSet.univ (SpecialTransformations.Section5.rawRVSpace C.arity) B.real))
      (gamma_raw_contraction_domain C (gamma_program_final_set C.program hC))
    intro u
    rfl
  · intro u
    exact congrArg (fun t : Fin (n+k) → RV (M := M) => rawWeight (fun j => (t j).val))
      (rawSelectedNormalization_volume C ρ u).symm

theorem gammaRawSelectedNormalizationIso_volume {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U)) (ρ : Fin k → Fin a)
    (hfin : ∀ (x : Fin n → VF (M := M)) (t : Fin k → RV (M := M)),
      {r : Fin a → RV (M := M) | (x,r) ∈ carrier U ∧ r ∘ ρ = t}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program)
    (u : rvObjectDomain (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC).object) :
    gammaVolumeValue (gammaFiniteSelectedContraction hκ hs hreal hBS hU ρ hfin C hC).toGammaRVObject
        ((gammaRawSelectedNormalizationIso hκ hs hreal hBS hU ρ hfin C hC).equiv u) =
      gammaVolumeValue (gammaRawSelectedContraction hκ hs hreal hBS hU ρ hfin C hC).toGammaRVObject u :=
  rawSelectedNormalization_volume C ρ u

end IntegrationInACVF.Section6.FiniteRV
