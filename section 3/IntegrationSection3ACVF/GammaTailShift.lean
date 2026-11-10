import IntegrationSection3ACVF.GammaTailIso
import IntegrationSection3ACVF.GammaSlopeValueGraph
import IntegrationSection3ACVF.GammaShiftConstancy

/-! The actual Gamma tail isomorphism has finite shift range and
finite controllers for every shift fibre. The proved order argument
therefore identifies its shift with the ratio of the ball radii. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.GammaTailMap

namespace IntegrationInACVF.Section3ACVF.GammaTailShift

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem shift_eq_coefficient (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) (γ : Set.Ioi α) :
    valueMap a α f hfVF hinj γ / γ.val = codeValue (coefficient a α f hfVF hinj γ) := by
  simp only [valueMap,mul_div_cancel_left]

theorem relation_shift (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (γ : Set.Ioi α) (η : Values.Gamma (M := M)) :
    GammaSlopeValueGraph.valueRelation (gammaBall a α true) f γ.val η ↔
      valueMap a α f hfVF hinj γ / γ.val = η := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hc := coefficient_spec a α f hfVF hinj γ
  constructor
  · rintro ⟨c,hc',he⟩
    have hEq := RVSlopeConstancy.on_value_fibre B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ.val hc hc'
    exact (shift_eq_coefficient a α f hfVF hinj γ).trans ((congrArg codeValue hEq).trans he)
  · intro he
    exact ⟨coefficient a α f hfVF hinj γ,hc,(shift_eq_coefficient a α f hfVF hinj γ).symm.trans he⟩

theorem finite_range {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    (Set.range (fun γ : Set.Ioi α => valueMap a α f hfVF hinj γ / γ.val)).Finite := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hF := RVSlopeGamma.finite_image hκ hs B hsmall h00 δ hδ hδ1 ho hA f hf hfVF hinj
  apply (hF.image (codeValue (M := M))).subset
  rintro η ⟨γ,rfl⟩
  exact ⟨coefficient a α f hfVF hinj γ,⟨γ.val,coefficient_spec a α f hfVF hinj γ⟩,
    (shift_eq_coefficient a α f hfVF hinj γ).symm⟩

theorem row_controller (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (η : Values.Gamma (M := M)) :
    ∃ F, FiniteOrder.Controls F {p | ∃ hp : α < p, valueMap a α f hfVF hinj ⟨p,hp⟩ / p = η} := by
  have hD := GammaSlopeValueGraph.row_controller h00 B hf η
  have he : {p | GammaSlopeValueGraph.valueRelation (gammaBall a α true) f p η} =
      {p | ∃ hp : α < p, valueMap a α f hfVF hinj ⟨p,hp⟩ / p = η} := by
    ext p
    constructor
    · rintro ⟨c,hc,he⟩
      have hp : α < p := (GammaSlopeDomain.domain_iff a α p f hfVF hinj).mp ⟨c,hc⟩
      exact ⟨hp,(relation_shift B h00 δ hδ hδ1 a α hA f hf hfVF hinj ⟨p,hp⟩ η).mp ⟨c,hc,he⟩⟩
    · rintro ⟨hp,he⟩
      exact (relation_shift B h00 δ hδ hδ1 a α hA f hf hfVF hinj ⟨p,hp⟩ η).mpr he
  exact he ▸ hD

theorem radius_ratio {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) :
    ∀ γ : Set.Ioi α, valueMap a α f hfVF hinj γ / γ.val = β/α := by
  let e := GammaTailIso.orderIso B h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage
  have he (γ : Set.Ioi α) : (e γ).val = valueMap a α f hfVF hinj γ := rfl
  have hF : (Set.range (fun γ : Set.Ioi α => (e γ).val / γ.val)).Finite := by
    simpa only [he] using finite_range hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj
  have hC : ∀ η, ∃ F, FiniteOrder.Controls F {p | ∃ hp : α < p, (e ⟨p,hp⟩).val / p = η} := by
    intro η
    simpa only [he] using row_controller B h00 δ hδ hδ1 a α hA f hf hfVF hinj η
  have hR := GammaShiftConstancy.radius_ratio α β e (GammaShiftConstancy.shift_constant α β e hF hC)
  simpa only [he] using hR

end IntegrationInACVF.Section3ACVF.GammaTailShift
