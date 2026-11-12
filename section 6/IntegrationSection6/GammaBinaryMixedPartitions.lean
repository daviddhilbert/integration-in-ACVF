import IntegrationSection6.GammaFiniteMixedUnions

/-! The actual binary partition by a Gamma predicate and its complement. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n a : ℕ}

def binaryMixedPieces (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (b : Bool) : DefSet (M := M) Set.univ n a :=
  if b then gammaDefSetUniv (carrier A \ D) ((gammaLogicInput B).sdiff hA hD) else gammaDefSetUniv D hD

theorem binaryMixedPieces_definable (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (b : Bool) :
    GammaSetDefinable B (carrier (binaryMixedPieces A hA D hD b)) := by
  cases b
  · exact hD
  · exact (gammaLogicInput B).sdiff hA hD

theorem binaryMixedPieces_subset (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (hDA : D ⊆ carrier A) (b : Bool) :
    carrier (binaryMixedPieces A hA D hD b) ⊆ carrier A := by
  cases b
  · exact hDA
  · exact fun _ h => h.1

theorem binaryMixedPieces_disjoint (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (i j : Bool) (hij : i ≠ j) :
    Disjoint (carrier (binaryMixedPieces A hA D hD i)) (carrier (binaryMixedPieces A hA D hD j)) := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact Set.disjoint_left.mpr (fun _ hD hE => hE.2 hD)
  · exact Set.disjoint_left.mpr (fun _ hE hD => hE.2 hD)
  · exact (hij rfl).elim

theorem binaryMixedPieces_cover (A : DefSet (M := M) Set.univ n a) (hA : GammaSetDefinable B (carrier A))
    (D : Set (Point (M := M) n a)) (hD : GammaSetDefinable B D) (hDA : D ⊆ carrier A) :
    carrier A = mixedFiniteUnionSet (binaryMixedPieces A hA D hD) Finset.univ := by
  ext p
  constructor
  · intro hp
    by_cases h : p ∈ D
    · exact ⟨false,Finset.mem_univ _,h⟩
    · exact ⟨true,Finset.mem_univ _,hp,h⟩
  · rintro ⟨b,_,hp⟩
    exact binaryMixedPieces_subset A hA D hD hDA b hp

theorem mixedFiniteUnionSet_bool (D : Bool → DefSet (M := M) Set.univ n a) :
    mixedFiniteUnionSet D Finset.univ = carrier (D false) ∪ carrier (D true) := by
  ext p
  constructor
  · rintro ⟨b,_,hp⟩
    cases b
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (hp | hp)
    · exact ⟨false,Finset.mem_univ _,hp⟩
    · exact ⟨true,Finset.mem_univ _,hp⟩

end IntegrationInACVF.Section6
