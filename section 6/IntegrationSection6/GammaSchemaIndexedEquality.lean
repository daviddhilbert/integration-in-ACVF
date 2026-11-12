import IntegrationSection6.GammaSchemaIndexedObjects
import IntegrationSection6.GammaSchemaPresentationEquality

/-! Equal formula rows give the actual label-identity isomorphism after
indexed assembly, even when the two schemata carry different bounds. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p a d k : ℕ} {sp : Fin p → SortTag}

theorem GammaFiniteRVSchema.rowValue_eq_of_sameRow (F G : GammaFiniteRVSchema B p a k sp)
    (z : Fin p → M) (h : F.sameRow G z) : F.rowValue z = G.rowValue z := by
  have hV := F.sameRow_volumes G h
  funext x
  by_cases hF : ∃! y : Fin k → RV (M := M), F.rowVolume z x y
  · have hG : ∃! y : Fin k → RV (M := M), G.rowVolume z x y := by
      rw [← hV]
      exact hF
    have hsF : F.rowVolume z x (F.rowValue z x) := by
      unfold GammaFiniteRVSchema.rowValue
      rw [dif_pos hF]
      exact hF.exists.choose_spec
    have hsG : G.rowVolume z x (G.rowValue z x) := by
      unfold GammaFiniteRVSchema.rowValue
      rw [dif_pos hG]
      exact hG.exists.choose_spec
    apply hF.unique hsF
    rw [hV]
    exact hsG
  · have hG : ¬ ∃! y : Fin k → RV (M := M), G.rowVolume z x y := by
      rw [← hV]
      exact hF
    simp only [GammaFiniteRVSchema.rowValue,dif_neg hF,dif_neg hG]

variable {T : Set (Fin p → RV (M := M))}
variable {R : (Fin p → RV (M := M)) → (Fin d → RV (M := M)) → Prop}

def GammaFiniteRVSchema.indexedRowIso
    (F G : GammaFiniteRVSchema B p a k (fun _ => .rv))
    (BP : GammaFiniteGraphPresentation B p d T R)
    (hEq : ∀ t ∈ T, F.sameRow G (fun j => (t j).val))
    (P : GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y))
    (Q : GammaFiniteGraphPresentation B (p+a) (d+k)
      (indexedDomain T (fun t => G.rowDomain (fun j => (t j).val)))
      (fun w y => w ∈ indexedDomain T (fun t => G.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => G.rowValue (fun j => (t j).val)) w = y)) :
    GammaRVIso P.toGamma.toGammaRVObject Q.toGamma.toGammaRVObject := by
  have hD : indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) =
      indexedDomain T (fun t => G.rowDomain (fun j => (t j).val)) := by
    apply Set.ext
    intro w
    constructor
    · rintro ⟨ht,hx⟩
      exact ⟨ht,(Set.ext_iff.mp (F.sameRow_domains G (hEq _ ht)) _).mp hx⟩
    · rintro ⟨ht,hx⟩
      exact ⟨ht,(Set.ext_iff.mp (F.sameRow_domains G (hEq _ ht)) _).mpr hx⟩
  have hR : ∀ w y,
      (w ∈ indexedDomain T (fun t => F.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w = y) ↔
      (w ∈ indexedDomain T (fun t => G.rowDomain (fun j => (t j).val)) ∧
        indexedVolume BP.totalVolume (fun t => G.rowValue (fun j => (t j).val)) w = y) := by
    intro w y
    by_cases ht : indexedLeft w ∈ T
    · have hValue := F.rowValue_eq_of_sameRow G _ (hEq _ ht)
      have hV : indexedVolume BP.totalVolume (fun t => F.rowValue (fun j => (t j).val)) w =
          indexedVolume BP.totalVolume (fun t => G.rowValue (fun j => (t j).val)) w :=
        congrArg (fun v : Fin k → RV (M := M) => Fin.append (BP.totalVolume (indexedLeft w)) v)
          (congrFun hValue (indexedRight w))
      rw [hD,hV]
    · exact ⟨fun h => False.elim (ht h.1.1),fun h => False.elim (ht h.1.1)⟩
  have e := gammaGraphPresentationIso (P.congrFormula hD hR) Q
  rw [GammaFiniteGraphPresentation.congrFormula_toGamma] at e
  exact e

end IntegrationInACVF.Section6
