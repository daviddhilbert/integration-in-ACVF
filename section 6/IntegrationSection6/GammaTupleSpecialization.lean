import IntegrationSection6.GammaTuplePromotion
import Section3.GammaRealMap

/-! Specialize a promoted tuple family at its actual named real tuple.
All original Gamma names and full proper-code invariance are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem gamma_tuple_parameter_specialize (sa : Fin n → SortTag) (sb : Fin m → SortTag)
    (a : Fin n → M) {P : Set (Fin (n+m) → M)} (hP : DefinableOverBase B (Fin.append sa sb) P) :
    DefinableOverBase ⟨B.real ∪ Set.range a,B.gamma⟩ sb {z | Fin.append a z ∈ P} := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range a,B.gamma⟩
  let R := B.real ∪ Set.range a
  have hPC : DefinableOverBase C (Fin.append sa sb) P := hP.mono Set.subset_union_left (Set.Subset.refl _)
  have hF : @Set.DefinableMap M LRV N (Fin m) (Fin (n+m)) R (fun z => Fin.append a z) := by
    letI := N
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · simp only [Fin.append_left]
      exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · simp only [Fin.append_right]
      exact Set.DefinableFun.proj LRV
  have h := hPC.preimage_real_map sb (fun z => Fin.append a z) hF
  convert h using 1
  ext z
  constructor
  · intro hz
    refine ⟨hz,fun j => ?_⟩
    simpa only [Fin.append_right] using hPC.proper _ hz (Fin.natAdd n j)
  · exact And.left

end IntegrationInACVF.Section6
