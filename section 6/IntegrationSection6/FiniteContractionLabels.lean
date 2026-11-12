import IntegrationSection6.FiniteStandardContractions
import IntegrationSection6.FiniteVolumeAugmentation

/-! The E union I_n volume in6.14 is represented literally: retain the
n contraction volumes and append the chosen original RV coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6.FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n m e : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) S n m}
variable {σ : Equiv.Perm (Fin n)}
local notation "N" => (@CanonicalStructure.normalize M sM)

def contractionOldLabelIndex (C : StandardContraction A σ) (j : Fin m) : Fin (n+C.arity) :=
  Fin.natAdd n (suffixIndex C.program.rvArity_le j)

theorem contraction_oldLabels (C : StandardContraction A σ) (a : A) (j : Fin m) :
    (C.normalizedContractionMap a).val (contractionOldLabelIndex C j) = a.val.2 j := by
  calc
    _ = (C.rawContractionMap a).val (suffixIndex C.program.rvArity_le j) :=
      toFirstVolume_oldLabels _ _ _ _
    _ = a.val.2 j := C.program.oldLabels (vfPermutationBijection A σ a) j

def gammaFiniteContractionLabels {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    (hA : GammaSetDefinable B (carrier A))
    (hfin : ∀ x : Fin n → VF (M := M), {r : Fin m → RV (M := M) | (x,r) ∈ carrier A}.Finite)
    (C : StandardContraction A σ) (hC : GammaProgramDefinable B C.program) (ρ : Fin e → Fin m) :
    GammaRVFiniteObject B (n+e) :=
  ((gammaObjectAtExtend (gammaFiniteContraction hκ hs hsmall hBS hA hfin C hC)
    (Set.Subset.refl S)).addVolumeLabels (fun j => contractionOldLabelIndex C (ρ j))).toGamma

theorem contraction_selectedLabels (C : StandardContraction A σ) (ρ : Fin e → Fin m) (a : A) :
    (fun j => (C.normalizedContractionMap a).val (contractionOldLabelIndex C (ρ j))) =
      (fun j => a.val.2 (ρ j)) := by
  funext j
  exact contraction_oldLabels C a (ρ j)

end IntegrationInACVF.Section6.FiniteRV
