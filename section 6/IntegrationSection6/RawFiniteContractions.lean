import IntegrationSection6.GammaRawStandardContractions
import IntegrationSection6.FiniteStandardContractions
import IntegrationSection6.FiniteGammaIsoLaws

/-! Finite-volume certificates and exact volume-preserving normalization
for the raw final labels of ordinary standard contractions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n a : ℕ}
variable {U : DefSet (M := M) S n a} {σ : Equiv.Perm (Fin n)}

def gammaRawFiniteContraction {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program) : GammaRVFiniteObject B n where
  toGammaRVObject := gammaRawContractionObject C hBS (gamma_program_final_set C.program hC)
  finite_volume := by
    let Q := gammaFiniteContraction hκ hs hreal hBS hU hfin C hC
    intro t
    apply (Q.finite_volume t).of_injOn (f := toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex)
    · intro u hu
      apply Subtype.ext
      exact (toFirstVolume_volume _ _ u).trans (congrArg Subtype.val hu)
    · intro u hu v hv he
      exact (toFirstVolume_bijective _ _).1 he

def gammaRawFiniteNormalizationIso {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hU : GammaSetDefinable B (carrier U))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin a → RV (M := M) | (x,r) ∈ carrier U}.Finite)
    (C : StandardContraction U σ) (hC : GammaProgramDefinable B C.program) :
    GammaRVIso (gammaRawFiniteContraction hκ hs hreal hBS hU hfin C hC).toGammaRVObject
      (gammaFiniteContraction hκ hs hreal hBS hU hfin C hC).toGammaRVObject := by
  let F := toFirstVolume (Map.image (rawLabelMap C.target)) C.volumeIndex
  apply gammaIsoOfFiniteEquiv _ _ (Equiv.ofBijective F (toFirstVolume_bijective _ _))
  · apply gamma_rv_graph_of_global_formula F
      (@rawRVProjectionMap M sM hM B.real C.arity (n+C.arity)
        (prependVolumeIndex C.volumeIndex) (PresentedSet.univ (SpecialTransformations.Section5.rawRVSpace C.arity) B.real))
      (gamma_raw_contraction_domain C (gamma_program_final_set C.program hC))
    intro u
    rfl
  · intro u
    exact congrArg (fun t : Fin n → RV (M := M) => rawWeight (fun j => (t j).val))
      (toFirstVolume_volume _ _ u).symm

end IntegrationInACVF.Section6.FiniteRV
