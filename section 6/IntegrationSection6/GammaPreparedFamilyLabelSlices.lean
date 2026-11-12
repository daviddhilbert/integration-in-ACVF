import IntegrationSection6.GammaPreparedFamilyValues
import IntegrationSection6.GammaNamedIsoRestrictions

/-! The actual prepared-family bijection preserves every original RV
label, so it restricts over precisely the selected named RV values. -/
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
variable {B : Base (M := M)} {p l a k d : ℕ}
variable {A : Set (Point (M := M) p 0)} {C : Set (Point (M := M) p l)}

theorem gammaPreparedFamilyIso_oldLabels (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (z : vfSchemaSource A F) :
    ((gammaPreparedFamilyIso e hA F).equiv z).val.2 ∘ Fin.natAdd (p+l) = z.val.2 := by
  have hv := gammaPreparedFamilyIso_value e hA F z
  funext j
  have h := congrArg (fun q : Point (M := M) p ((p+l)+a) => q.2 (Fin.natAdd (p+l) j)) hv
  simpa only [Function.comp_apply,Fin.append_right] using h

def gammaPreparedFamilyNamedLabels (e : GammaIso B A C) (hA : GammaSetDefinable B A)
    (F : GammaFiniteRVSchema B p a k) (ρ : Fin d → Fin a) (t : Fin d → RV (M := M)) :
    GammaIso ⟨B.real ∪ Set.range (fun j => (t j).val),B.gamma⟩
      (vfSchemaSource A F ∩ {q | q.2 ∘ ρ = t})
      (preparedFamilyImage e F ∩ {q | q.2 ∘ (fun j => Fin.natAdd (p+l) (ρ j)) = t}) := by
  apply gammaIsoNamedRVLabels (gammaPreparedFamilyIso e hA F) ρ (fun j => Fin.natAdd (p+l) (ρ j)) ?_ t
  intro z
  exact congrArg (fun r => r ∘ ρ) (gammaPreparedFamilyIso_oldLabels e hA F z)

end IntegrationInACVF.Section6
