import IntegrationSection6.IndexedCoproductEquivalences
import IntegrationSection6.GammaSchemaCoproductRowValues

/-! Indexed coproduct/index interchange preserves the actual appended
volume on both canonical summands. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a b d k : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

theorem indexedCoprodLeft_volume
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (T : Set (Fin p → RV (M := M))) (f : (Fin p → RV (M := M)) → (Fin d → RV (M := M)))
    (t : T) (x : F.rowDomain (fun j => (t.val j).val))
    (hF : F.finiteRow (fun j => (t.val j).val)) (hG : G.finiteRow (fun j => (t.val j).val)) :
    indexedVolume f (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val))
      (indexedCoprodLeft T (fun t => F.rowDomain (fun j => (t j).val))
        (fun t => G.rowDomain (fun j => (t j).val)) t x).val =
    indexedVolume f (fun t => F.rowValue (fun j => (t j).val))
      ((indexedSigmaEquiv T (fun t => F.rowDomain (fun j => (t j).val))).symm ⟨t,x⟩).val := by
  change indexedVolume f _ (Fin.append t.val (@rvLeftTag M N hN a b x.val)) =
    indexedVolume f _ (Fin.append t.val x.val)
  unfold indexedVolume
  simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  rw [F.rowValue_coprod_left G _ (fun j => (t.val j).property) hF hG x.val x.property]

theorem indexedCoprodRight_volume
    (F : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (G : GammaFiniteRVSchema B p b k (fun _ => .rv))
    (T : Set (Fin p → RV (M := M))) (f : (Fin p → RV (M := M)) → (Fin d → RV (M := M)))
    (t : T) (x : G.rowDomain (fun j => (t.val j).val))
    (hF : F.finiteRow (fun j => (t.val j).val)) (hG : G.finiteRow (fun j => (t.val j).val)) :
    indexedVolume f (fun t => (F.coprodFormula G).rowValue (fun j => (t j).val))
      (indexedCoprodRight T (fun t => F.rowDomain (fun j => (t j).val))
        (fun t => G.rowDomain (fun j => (t j).val)) t x).val =
    indexedVolume f (fun t => G.rowValue (fun j => (t j).val))
      ((indexedSigmaEquiv T (fun t => G.rowDomain (fun j => (t j).val))).symm ⟨t,x⟩).val := by
  change indexedVolume f _ (Fin.append t.val (@rvRightTag M N hN b a x.val)) =
    indexedVolume f _ (Fin.append t.val x.val)
  unfold indexedVolume
  simp only [indexedLeft,indexedRight,Function.comp_def,Fin.append_left,Fin.append_right]
  rw [F.rowValue_coprod_right G _ (fun j => (t.val j).property) hF hG x.val x.property]

end IntegrationInACVF.Section6
