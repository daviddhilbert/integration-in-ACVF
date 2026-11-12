import IntegrationSection6.GammaTupleSpecialization
import Section5.GammaGraphs

/-! Public tuple-code bridges for original-Gamma families. The elementary
injectivity argument follows the checked private bridge in the pinned
Section5.GammaBaseInputs; decoding is explicit on the sorted universe. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n m u w : ℕ}

omit hM in
theorem gammaPointCode_injective :
    Function.Injective (gammaPointCode (M := M) (n := n) (m := m)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode,vfAt,Fin.append_left] using congrFun h (Fin.castAdd m i)
  · funext i
    apply Subtype.ext
    simpa only [gammaPointCode,Fin.append_right] using congrFun h (Fin.natAdd n i)

def pointOfSortedCode (z : Fin (n+m) → M)
    (hz : ∀ i, sortEval (gammaPointSort n m i) (z i)) : Point (M := M) n m :=
  (fun i => ⟨z (Fin.castAdd m i),by simpa only [gammaPointSort,Fin.append_left,sortEval,iVF] using hz (Fin.castAdd m i)⟩,
   fun i => ⟨z (Fin.natAdd n i),by simpa only [gammaPointSort,Fin.append_right,sortEval,iRV] using hz (Fin.natAdd n i)⟩)

theorem pointOfSortedCode_code (z : Fin (n+m) → M)
    (hz : ∀ i, sortEval (gammaPointSort n m i) (z i)) :
    gammaPointCode (pointOfSortedCode z hz) = z := by
  exact Fin.append_castAdd_natAdd

theorem gamma_set_of_sorted_formula {P : Set (Fin (n+m) → M)}
    (hP : DefinableOverBase B (gammaPointSort n m) P) :
    GammaSetDefinable B {p : Point (M := M) n m | gammaPointCode p ∈ P} := by
  change DefinableOverBase B (gammaPointSort n m) _
  have he : gammaPointCode '' {p : Point (M := M) n m | gammaPointCode p ∈ P} = P := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact hp
    · intro hz
      exact ⟨pointOfSortedCode z (hP.proper z hz),by
        simpa only [Set.mem_ofPred_eq,pointOfSortedCode_code] using hz,pointOfSortedCode_code z _⟩
  rw [he]
  exact hP

theorem gamma_graph_of_sorted_formula {P : Set (Fin ((n+m)+(u+w)) → M)}
    (hP : DefinableOverBase B (Fin.append (gammaPointSort n m) (gammaPointSort u w)) P) :
    GammaGraphDefinable B (fun (p : Point (M := M) n m) (q : Point (M := M) u w) =>
      Fin.append (gammaPointCode p) (gammaPointCode q) ∈ P) := by
  change DefinableOverBase B (Fin.append (gammaPointSort n m) (gammaPointSort u w)) _
  have he : {z | ∃ p : Point (M := M) n m, ∃ q : Point (M := M) u w,
      Fin.append (gammaPointCode p) (gammaPointCode q) ∈ P ∧
      Fin.append (gammaPointCode p) (gammaPointCode q) = z} = P := by
    apply Set.ext
    intro z
    constructor
    · rintro ⟨p,q,hp,rfl⟩
      exact hp
    · intro hz
      have hl : ∀ i, sortEval (gammaPointSort n m i) ((z ∘ Fin.castAdd (u+w)) i) := by
        intro i
        simpa only [Function.comp_apply,Fin.append_left] using hP.proper z hz (Fin.castAdd (u+w) i)
      have hr : ∀ i, sortEval (gammaPointSort u w i) ((z ∘ Fin.natAdd (n+m)) i) := by
        intro i
        simpa only [Function.comp_apply,Fin.append_right] using hP.proper z hz (Fin.natAdd (n+m) i)
      refine ⟨pointOfSortedCode _ hl,pointOfSortedCode _ hr,?_,?_⟩
      · simpa only [pointOfSortedCode_code,Function.comp_def,Fin.append_castAdd_natAdd] using hz
      · rw [pointOfSortedCode_code,pointOfSortedCode_code]
        exact Fin.append_castAdd_natAdd
  rw [he]
  exact hP

end IntegrationInACVF.Section6
