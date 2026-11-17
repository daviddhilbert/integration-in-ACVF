module

public import Integration7.CompletedSection6Kernel
public import Integration7.ClosedSection6ParameterCoefficientClasses
public import Integration7.ClosedSection6DefinableFamilyRowObjects
public import IntegrationSection6.DefinableFamilyCoefficients
public import IntegrationSection6.ParameterCoefficientClasses
public import IntegrationSection6.DefinableFamilyRowObjects

set_option backward.privateInPublic true
set_option backward.proofsInPublic true
@[expose] public section

/-! Closed generated-base Section6 integration. The former universal
Section5 input is replaced by the canonical-model certificate; its kernel
uses the proved generated-base contraction comparison. Original finite
objects, actual lifting, scissor addition and Cartesian products are retained.
This module keeps the dependent data and consumers in one coherent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5 SpecialTransformations.Section7
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
namespace IntegrationInACVF.Section7.CompletedSection6
open FiniteRV
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {p : ℕ}
variable {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
variable (h00 : M ⊨ Axioms.ACVF00) (hr : Cardinal.mk B.real < κ) (hg : Cardinal.mk B.gamma < κ)
variable (FBase : VFFieldBase B.real) (hB : VFGammaGeneratedBase B)
variable (δ : Values.Gamma (M := M)) (hδ : δ ∈ B.gamma) (hδ1 : 1 < δ)
variable (hc : CanonicalStructure.IsCanonical (M := M))


def schemaRowLift {a k : ℕ} (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M)) :
    Set (Point (M := M) k a) := {q | F.rowVolume (fun j => (x j).val) q.2 (tupleRV q.1)}

def schemaRowCoefficient {a k : ℕ} (F : GammaFiniteRVSchema B p a k) (x : Fin p → VF (M := M))
    (hx : F.finiteRow (fun j => (x j).val)) :
    ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x :=
  parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x (schemaRowObject F x hx).toGamma

theorem schemaRowCoefficient_eq_iff {a b k l : ℕ}
    (F : GammaFiniteRVSchema B p a k) (G : GammaFiniteRVSchema B p b l)
    (x : Fin p → VF (M := M))
    (hF : F.finiteRow (fun j => (x j).val)) (hG : G.finiteRow (fun j => (x j).val)) :
    schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 hc F x hF =
      schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 hc G x hG ↔
        Nonempty (GammaIso ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
          (schemaRowLift F x) (schemaRowLift G x)) := by
  change parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x (schemaRowObject F x hF).toGamma =
    parameterRVClass hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x (schemaRowObject G x hG).toGamma ↔ _
  rw [parameterRVClass_eq_iff_liftIso]
  constructor
  · rintro ⟨e⟩
    exact ⟨gammaIsoClosureDescend (e.congr (schemaRowObject_lift F x hF) (schemaRowObject_lift G x hG))⟩
  · rintro ⟨e⟩
    let C : Base (M := M) := ⟨B.real ∪ Set.range (fun j => (x j).val),B.gamma⟩
    let f : GammaIso (closureBase C) (schemaRowLift F x) (schemaRowLift G x) :=
      ⟨e.equiv,e.graph.mono (subset_closureBase C).1 (subset_closureBase C).2⟩
    exact ⟨f.congr (schemaRowObject_lift F x hF).symm (schemaRowObject_lift G x hG).symm⟩

end IntegrationInACVF.Section7.CompletedSection6
