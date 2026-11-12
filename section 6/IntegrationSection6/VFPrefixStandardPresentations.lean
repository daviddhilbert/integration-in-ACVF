import IntegrationSection6.VFPrefixFibrePresentations
import IntegrationSection6.StandardProgramPresentations
import IntegrationSection6.GammaOrdinaryContractionPresentations

/-! Finite RV fibre presentations of a partial contraction give actual
standard-contraction presentations of the frozen VF prefix. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p a l k : ℕ}
variable {U : DefSet (M := M) S (n+p) a} {V : DefSet (M := M) S n l}

def prefixPartialStandardPresentation (T : PartialContractionProgram S n (n := p) U V)
    (ρ : Fin k → Fin a) (x : Fin n → VF (M := M))
    (A : DefSet (M := M) (S ∪ Set.range (fun j => (x j).val)) p a) (σ : Equiv.Perm (Fin p))
    (hA : vfPrefixFibre (n := n) (p := p) U x = vfPermutationImage A σ)
    (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T ρ) x) :
    GammaSelectedRVPresentation ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
      (standardFromProgram A σ (restrictPartialToPrefix T x) hA).target
      (orderedSelectedIndex (standardFromProgram A σ (restrictPartialToPrefix T x) hA).program ρ) :=
  (prefixPartialPresentation T ρ x P).congrFormula rfl (fun r y => and_congr Iff.rfl
    (Iff.of_eq (congrArg (fun θ => r ∘ θ = y)
      (standardFromProgram_selectedIndex A σ (restrictPartialToPrefix T x) hA ρ).symm)))

theorem prefixPartialStandardPresentation_toGamma (T : PartialContractionProgram S n (n := p) U V)
    (ρ : Fin k → Fin a) (x : Fin n → VF (M := M))
    (A : DefSet (M := M) (S ∪ Set.range (fun j => (x j).val)) p a) (σ : Equiv.Perm (Fin p))
    (hA : vfPrefixFibre (n := n) (p := p) U x = vfPermutationImage A σ)
    (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T ρ) x) :
    (prefixPartialStandardPresentation T ρ x A σ hA P).toGamma = P.toGamma := by
  simp only [prefixPartialStandardPresentation,GammaFiniteGraphPresentation.congrFormula_toGamma,
    prefixPartialPresentation_toGamma]

theorem prefixPartialTwoStandardComparison {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hreal : Cardinal.mk B.real < κ) (hBS : B.real ⊆ S)
    {U : DefSet (M := M) S (n+2) a} {V : DefSet (M := M) S n l}
    (T : PartialContractionProgram S n (n := 2) U V) (hT : GammaPartialProgramDefinable B T)
    (x : Fin n → VF (M := M))
    (A : DefSet (M := M) (S ∪ Set.range (fun j => (x j).val)) 2 a) (σ : Equiv.Perm (Fin 2))
    (hSource : vfPrefixFibre (n := n) (p := 2) U x = vfPermutationImage A σ)
    (hA : GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (carrier A))
    (hfinA : ∀ z : Fin 2 → VF (M := M), {r : Fin a → RV (M := M) | (z,r) ∈ carrier A}.Finite)
    (P : SelectedLabelFibrePresentation B V (partialSelectedIndex T (Fin.elim0 : Fin 0 → Fin a)) x) :
    ∃ C : StandardContraction A σ, ∃ hC : GammaProgramDefinable
      ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ C.program,
      Nonempty (GammaRVIso P.toGamma.toGammaRVObject
        (FiniteRV.gammaFiniteContraction hκ hs (small_union_range hκ B.real hreal (fun j => (x j).val))
          (Set.union_subset_union hBS (Set.Subset.refl _)) hA hfinA C hC).toGammaRVObject) := by
  let C := standardFromProgram A σ (restrictPartialToPrefix T x) hSource
  let hC := gamma_standardFromProgram A σ (restrictPartialToPrefix T x) hSource
    (gamma_restrictPartialToPrefix T hT x)
  let Q := prefixPartialStandardPresentation T (Fin.elim0 : Fin 0 → Fin a) x A σ hSource P
  have e := FiniteRV.gammaOrdinaryContractionPresentationIso hκ hs
    (small_union_range hκ B.real hreal (fun j => (x j).val))
    (Set.union_subset_union hBS (Set.Subset.refl _)) hA hfinA C hC Q
  refine ⟨C,hC,?_⟩
  simpa only [Q,prefixPartialStandardPresentation_toGamma,orderedVolumeDegree,gammaCastDegree] using Nonempty.intro e

end IntegrationInACVF.Section6
