import IntegrationSection6.ParameterCoefficientClasses
import IntegrationSection6.DefinableFamilyRowObjects

/-! Definable RV families take values in the actual varying coefficient
semirings; equality is exactly a definable isomorphism of row lifts. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
variable (FBase : VFFieldBase B.real) (hB : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (h58 : Section5TwoOrderInputAll hκ hs)

def schemaRowLift {a k : ℕ} (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M)) :
    Set (Point (M := M) k a) := {q | F.rowVolume (fun j => (x j).val) q.2 (tupleRV q.1)}

def schemaRowCoefficient {a k : ℕ} (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) :
    ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x :=
  parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x (schemaRowObject F x hx).toGamma

theorem schemaRowCoefficient_eq_iff {a b k l : ℕ}
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M))
    (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 F x hF =
      schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 G x hG ↔
        Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
          (schemaRowLift F x) (schemaRowLift G x)) := by
  change parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x (schemaRowObject F x hF).toGamma =
    parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 h58 x (schemaRowObject G x hG).toGamma ↔ _
  rw [parameterRVClass_eq_iff_liftIso]
  constructor
  · rintro ⟨e⟩
    exact ⟨gammaIsoClosureDescend (e.congr (schemaRowObject_lift F x hF) (schemaRowObject_lift G x hG))⟩
  · rintro ⟨e⟩
    let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
    let f : GammaIso (closureBase C) (schemaRowLift F x) (schemaRowLift G x) :=
      ⟨e.equiv,e.graph.mono (subset_closureBase C).1 (subset_closureBase C).2⟩
    exact ⟨f.congr (schemaRowObject_lift F x hF).symm (schemaRowObject_lift G x hG).symm⟩

end IntegrationInACVF.Section6
