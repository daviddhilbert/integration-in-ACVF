import Integration7.CompletedSection6Kernel
import Integration7.ClosedSection6DefinableFamilyIntegration
import IntegrationSection6.DefinableRVFunctions
import IntegrationSection6.DefinableFamilyIntegration

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


structure DefinableRVFamily (B : Base (M := M)) (A : Set (Point (M := M) p 0)) where
  arity : ℕ
  degree : ℕ
  schema : GammaFiniteRVSchema B p arity degree
  finite : ∀ x : A, schema.finiteRow (fun j => (x.val.1 j).val)

def definableRVFamilyValue {A : Set (Point (M := M) p 0)} (F : DefinableRVFamily B A) :
    ∀ x : A, ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x.val.1 :=
  fun x => schemaRowCoefficient hκ hs h00 hr hg FBase hB δ hδ hδ1 hc F.schema x.val.1 (F.finite x)

def definableRVFamilySetoid (A : Set (Point (M := M) p 0)) : Setoid (DefinableRVFamily B A) where
  r F G := ∀ x : A, definableRVFamilyValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc F x =
    definableRVFamilyValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc G x
  iseqv := ⟨fun _ _ => rfl,fun h x => (h x).symm,fun h g x => (h x).trans (g x)⟩

abbrev DefinableRVFunction (A : Set (Point (M := M) p 0)) :=
  Quotient (definableRVFamilySetoid hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A)

def definableRVFunctionValue (A : Set (Point (M := M) p 0)) :
    DefinableRVFunction hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A →
      ∀ x : A, ParameterCoefficientSemiring hκ hs h00 hr hg FBase hB δ hδ hδ1 hc x.val.1 :=
  Quotient.lift (definableRVFamilyValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc) (fun _ _ he => funext he)

theorem definableRVFunction_ext (A : Set (Point (M := M) p 0))
    (f g : DefinableRVFunction hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A)
    (he : ∀ x : A, definableRVFunctionValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A f x =
      definableRVFunctionValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A g x) : f = g := by
  induction f using Quotient.inductionOn with
  | h F =>
    induction g using Quotient.inductionOn with
    | h G => exact Quotient.sound he

def definableFunctionIntegral (A : Set (Point (M := M) p 0)) (hA : GammaSetDefinable B A) :
    DefinableRVFunction hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A →
      GlobalIntegrationSemiringTarget hκ hs h00 hr FBase hg δ hδ hδ1 hc hB :=
  Quotient.lift (fun F => familyIntegralValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A hA F.schema F.finite)
    (fun F G he => remark_6_20_representative_independence hκ hs h00 hr hg FBase hB δ hδ hδ1 hc
      A hA F.schema G.schema F.finite G.finite he)

theorem definableFunctionIntegral_representative (A : Set (Point (M := M) p 0))
    (hA : GammaSetDefinable B A) (F : DefinableRVFamily B A) :
    definableFunctionIntegral hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A hA (Quotient.mk _ F) =
      familyIntegralValue hκ hs h00 hr hg FBase hB δ hδ hδ1 hc A hA F.schema F.finite := rfl

end IntegrationInACVF.Section7.CompletedSection6
