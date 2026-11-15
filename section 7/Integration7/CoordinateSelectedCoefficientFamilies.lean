import Integration7.SelectedVolumeFamilyPositiveProducts

/-! A constant coefficient whose volume tuple is already given by literal
labels needs no further selection graph in the product family. Finiteness
is inherited from the genuine constant-family product. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.DefinableGeometry
namespace IntegrationInACVF.Section7
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {C : BaseContext M} {n a k p : ℕ}
variable (F : SelectedVFVolumeFamily C n a k)
variable (U : PositiveRVVolumeObject (M := M) (C.base : Set M) p)
variable (σ : Fin (p+1) → Fin U.underlying.obj.arity)
variable (hσ : ∀ u : U.underlying.obj.domain, U.underlying.obj.value u=u.val ∘ σ)

include hσ in
theorem coordinate_selected_coefficient_volume
    (q : mixedRVFactorDomain F.domain U.underlying.obj.domain) :
    (volumeFamilyConstantVolumeMap F.toDefinable U q).val =
      q.val.2 ∘ Fin.append (Fin.natAdd a ∘ σ) (Fin.castAdd U.underlying.obj.arity ∘ F.selected) := by
  have hu := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q)
  have hf := congrArg (fun w => w.1.2) (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q)
  change (volumeFamilyConstantCoefficientProjection F.toDefinable U q).val=q.val.2 ∘ Fin.natAdd a at hu
  change (volumeFamilyConstantBaseProjection F.toDefinable U q).val.2=q.val.2 ∘ Fin.castAdd U.underlying.obj.arity at hf
  rw [volume_family_constant_volume,hσ]
  change Fin.append ((volumeFamilyConstantCoefficientProjection F.toDefinable U q).val ∘ σ)
    ((volumeFamilyConstantBaseProjection F.toDefinable U q).val.2 ∘ F.selected) = _
  rw [hu,hf]
  funext i
  exact Fin.addCases (m := p+1) (n := k+1)
    (fun j => by simp only [Function.comp_apply,Fin.append_left])
    (fun j => by simp only [Function.comp_apply,Fin.append_right]) i

def coordinateSelectedCoefficientFamily : SelectedVFVolumeFamily C n (a+U.underlying.obj.arity) ((p+1)+k) where
  domain := mixedRVFactorDomain F.domain U.underlying.obj.domain
  selected := Fin.append (m := p+1) (n := k+1)
    (Fin.natAdd a ∘ σ) (Fin.castAdd U.underlying.obj.arity ∘ F.selected)
  finite_selected x t := ((F.toDefinable.mulConstant U).finite_volume x t).subset (by
    rintro r ⟨hr,ht⟩
    refine ⟨⟨(x,r),hr⟩,rfl,?_⟩
    exact (coordinate_selected_coefficient_volume F U σ hσ ⟨(x,r),hr⟩).trans ht)
  form := volumeFamilyConstantForm F.toDefinable U

theorem coordinate_selected_coefficient_density
    (δ : Fin a) (ε : Fin U.underlying.obj.arity)
    (hF : ∀ q : F.domain, F.form.value q=q.val.2 δ)
    (hU : ∀ u : U.underlying.obj.domain, U.form.value u=u.val ε)
    (q : (coordinateSelectedCoefficientFamily F U σ hσ).domain) :
    (coordinateSelectedCoefficientFamily F U σ hσ).form.value q =
      q.val.2 (Fin.natAdd a ε) * q.val.2 (Fin.castAdd U.underlying.obj.arity δ) := by
  change (volumeFamilyConstantForm F.toDefinable U).value q = _
  rw [volume_family_constant_density,hU]
  change (volumeFamilyConstantCoefficientProjection F.toDefinable U q).val ε *
    F.form.value (volumeFamilyConstantBaseProjection F.toDefinable U q) = _
  rw [hF]
  have hu := congrArg Prod.snd (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q)
  have hf := congrArg (fun w => w.1.2) (mixed_rv_factor_unpack_value F.domain U.underlying.obj.domain q)
  change (volumeFamilyConstantCoefficientProjection F.toDefinable U q).val=q.val.2 ∘ Fin.natAdd a at hu
  change (volumeFamilyConstantBaseProjection F.toDefinable U q).val.2=q.val.2 ∘ Fin.castAdd U.underlying.obj.arity at hf
  change (volumeFamilyConstantCoefficientProjection F.toDefinable U q).val ε *
    (volumeFamilyConstantBaseProjection F.toDefinable U q).val.2 δ = _
  rw [hu,hf]
  rfl
end IntegrationInACVF.Section7
