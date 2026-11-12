import IntegrationSection6.GammaElementaryFamilies
import IntegrationSection6.GammaRVGraphRaw
import IntegrationSection6.FiniteGammaBasicFactors

/-! Literal coordinate programs for elementary blowups of sorted raw
families. Parameters retain their original sorts and their coordinates. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def rawElementaryHead (p a : ℕ) : Fin (p+a) → Fin (p+(a+1)) :=
  Fin.addCases (Fin.castAdd (a+1)) (fun j => Fin.natAdd p (Fin.castAdd 1 j))

def rawElementaryParameter (p a : ℕ) : Fin 1 → Fin (p+(a+1)) :=
  fun j => Fin.natAdd p (Fin.natAdd a j)

def rawPositiveDomain (B : Base (M := M)) : Set (Fin 1 → M) :=
  gammaRawObjectDomain (FiniteRV.gammaPositiveAt (B := B) (S := B.real) (Set.Subset.refl _)).toGamma.toGammaRVObject

theorem rawPositiveDomain_definable (B : Base (M := M)) :
    DefinableOverBase B (fun _ : Fin 1 => .rv) (rawPositiveDomain B) :=
  gammaRawObjectDomain_definable
    (FiniteRV.gammaPositiveAt (B := B) (S := B.real) (Set.Subset.refl _)).toGamma.toGammaRVObject

def rawBlowupVolumeGraph (B : Base (M := M)) {k : ℕ} (i : Fin k) : Set (Fin ((k+1)+k) → M) :=
  gammaRawRVGraph (fun r q => (familyBlowupVolumeMap B.real i ⟨r,Set.mem_univ _⟩).val = q)

theorem rawBlowupVolumeGraph_definable (B : Base (M := M)) {k : ℕ} (i : Fin k) :
    DefinableOverBase B (fun _ : Fin ((k+1)+k) => .rv) (rawBlowupVolumeGraph B i) :=
  gammaRawRVGraph_definable (gamma_global_map_graph _)

theorem rawElementaryHead_append {Y : Type*} {p a : ℕ}
    (z : Fin p → Y) (x : Fin (a+1) → Y) :
    Fin.append z x ∘ rawElementaryHead p a = Fin.append z (x ∘ Fin.castAdd 1) := by
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
    simp only [Function.comp_apply,rawElementaryHead,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

theorem rawElementaryParameter_append {Y : Type*} {p a : ℕ}
    (z : Fin p → Y) (x : Fin (a+1) → Y) :
    Fin.append z x ∘ rawElementaryParameter p a = x ∘ Fin.natAdd a := by
  funext j
  exact Fin.append_right z x _

end IntegrationInACVF.Section6
