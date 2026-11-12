import IntegrationSection6.VFPrefixMaps
import IntegrationSection5.GammaCoordinateFibres

/-! Freezing a complementary VF tuple adds exactly its names to the
mathematical Gamma base, independently of internal real code sets. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {S : Set M} {n p m : ℕ}

theorem gamma_vfPrefix_preimage {A : Set (Point (M := M) (n+p) m)}
    (hA : GammaSetDefinable B A) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ {q | vfPrefixInsert x q ∈ A} := by
  let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
  have hA' : GammaSetDefinable C A := hA.mono Set.subset_union_left (Set.Subset.refl _)
  have h := (gammaLogicInput C).preimage_real (vfPrefixInsertMap B.real x p m) hA'
  convert h using 1
  ext q
  constructor
  · intro hq
    exact ⟨⟨q,Set.mem_univ _⟩,rfl,hq⟩
  · rintro ⟨a,ha,hax⟩
    exact ha ▸ hax

theorem gamma_vfPrefixFibre (A : DefSet (M := M) S (n+p) m)
    (hA : GammaSetDefinable B (carrier A)) (x : Fin n → VF (M := M)) :
    GammaSetDefinable ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩ (carrier (vfPrefixFibre A x)) :=
  gamma_vfPrefix_preimage hA x

end IntegrationInACVF.Section6
