import IntegrationSection6.GammaRawLabelImageRows
import IntegrationSection6.GammaCoproductFamilies
import IntegrationSection6.GammaGraphCoproducts

/-! Native tagged coproduct schemata with arbitrary sorted parameters.
The tags act only on object labels, preserving the parameter tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)

def rawLeftTagGraph (B : Base (M := M)) (a b : ℕ) : Set (Fin (a+(1+(a+b))) → M) :=
  gammaRawRVGraph (fun x w => (familyLeftTagMap B.real 0 a b ⟨x,Set.mem_univ _⟩).val = w)

def rawRightTagGraph (B : Base (M := M)) (a b : ℕ) : Set (Fin (b+(1+(a+b))) → M) :=
  gammaRawRVGraph (fun x w => (familyRightTagMap B.real 0 a b ⟨x,Set.mem_univ _⟩).val = w)

theorem rawLeftTagGraph_definable (B : Base (M := M)) (a b : ℕ) :
    DefinableOverBase B (fun _ => .rv) (rawLeftTagGraph B a b) :=
  gammaRawRVGraph_definable (gamma_global_map_graph _)

theorem rawRightTagGraph_definable (B : Base (M := M)) (a b : ℕ) :
    DefinableOverBase B (fun _ => .rv) (rawRightTagGraph B a b) :=
  gammaRawRVGraph_definable (gamma_global_map_graph _)

theorem rawLeftTagGraph_tuple_iff (B : Base (M := M)) {a b : ℕ}
    (x : Fin a → RV (M := M)) (w : Fin (1+(a+b)) → RV (M := M)) :
    Fin.append (fun j => (x j).val) (fun j => (w j).val) ∈ rawLeftTagGraph B a b ↔
      @rvLeftTag M N hN a b x = w := by
  have h := gammaRawRVGraph_append_iff
    (fun x w => (familyLeftTagMap B.real 0 a b ⟨x,Set.mem_univ _⟩).val = w)
    (Fin.elim0,x) (Fin.elim0,w)
  change _ ↔ _ at h
  exact h.trans ⟨fun he => congrArg Prod.snd he,fun he => Prod.ext (Subsingleton.elim _ _) he⟩

theorem rawRightTagGraph_tuple_iff (B : Base (M := M)) {a b : ℕ}
    (x : Fin b → RV (M := M)) (w : Fin (1+(a+b)) → RV (M := M)) :
    Fin.append (fun j => (x j).val) (fun j => (w j).val) ∈ rawRightTagGraph B a b ↔
      @rvRightTag M N hN b a x = w := by
  have h := gammaRawRVGraph_append_iff
    (fun x w => (familyRightTagMap B.real 0 a b ⟨x,Set.mem_univ _⟩).val = w)
    (Fin.elim0,x) (Fin.elim0,w)
  exact h.trans ⟨fun he => congrArg Prod.snd he,fun he => Prod.ext (Subsingleton.elim _ _) he⟩

variable {B : Base (M := M)} {p a b k : ℕ} {sp : Fin p → SortTag}

def GammaFiniteRVSchema.coprodFormula (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) : GammaFiniteRVSchema B p (1+(a+b)) k sp :=
  (F.labelImageFormula (rawLeftTagGraph_definable B a b)).unionFormula
    (G.labelImageFormula (rawRightTagGraph_definable B a b))

theorem GammaFiniteRVSchema.coprod_row_domain_formula (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (w : Fin (1+(a+b)) → RV (M := M)) :
    w ∈ (F.coprodFormula G).rowDomain z ↔ w ∈ graphCoprodDomain (F.rowDomain z) (G.rowDomain z) := by
  change (w ∈ (F.labelImageFormula (rawLeftTagGraph_definable B a b)).rowDomain z ∨
    w ∈ (G.labelImageFormula (rawRightTagGraph_definable B a b)).rowDomain z) ↔ _
  rw [F.labelImage_row_domain _ z hz w,G.labelImage_row_domain _ z hz w]
  change _ ↔ ((∃ x, _ ∧ _) ∨ ∃ y, _ ∧ _)
  exact or_congr (exists_congr (fun x => and_congr Iff.rfl (rawLeftTagGraph_tuple_iff B x w)))
    (exists_congr (fun x => and_congr Iff.rfl (rawRightTagGraph_tuple_iff B x w)))

theorem GammaFiniteRVSchema.coprod_row_volume_formula (F : GammaFiniteRVSchema B p a k sp)
    (G : GammaFiniteRVSchema B p b k sp) (z : Fin p → M) (hz : ∀ j, sortEval (sp j) (z j))
    (w : Fin (1+(a+b)) → RV (M := M)) (v : Fin k → RV (M := M)) :
    (F.coprodFormula G).rowVolume z w v ↔
      (∃ x, F.rowVolume z x v ∧ @rvLeftTag M N hN a b x = w) ∨
        ∃ x, G.rowVolume z x v ∧ @rvRightTag M N hN b a x = w := by
  change ((F.labelImageFormula (rawLeftTagGraph_definable B a b)).rowVolume z w v ∨
    (G.labelImageFormula (rawRightTagGraph_definable B a b)).rowVolume z w v) ↔ _
  rw [F.labelImage_row_volume _ z hz w v,G.labelImage_row_volume _ z hz w v]
  exact or_congr (exists_congr (fun x => and_congr Iff.rfl (rawLeftTagGraph_tuple_iff B x w)))
    (exists_congr (fun x => and_congr Iff.rfl (rawRightTagGraph_tuple_iff B x w)))

end IntegrationInACVF.Section6
