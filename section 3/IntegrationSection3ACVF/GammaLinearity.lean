import IntegrationSection3ACVF.GammaTailShift
import IntegrationSection3ACVF.PaperBallInvariants

/-! Lemma 3.16 on actual atomic open balls. The value-group operation
is multiplicative in Lean, so subtraction of radii is the ratio beta/alpha.
The finite-image step retains genuine saturation and smallness hypotheses. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.GammaTailMap

namespace IntegrationInACVF.Section3ACVF.GammaLinearity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def GammaLinear (A : Set M) (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (s : Values.Gamma (M := M)) : Prop :=
  ∀ (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A),
    let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
    let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
    Values.vfValueHom (fy-fx) = s.val * Values.vfValueHom (y-x)

theorem ordinary {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) :
    GammaLinear (gammaBall a α true) f hfVF (β/α) := by
  intro x y hx hy
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  change Values.vfValueHom (fy-fx) = (β/α).val * Values.vfValueHom (y-x)
  by_cases he : y = x
  · subst y
    change Values.vfValueHom (fx-fx) = (β/α).val * Values.vfValueHom (x-x)
    rw [sub_self,sub_self,map_zero,mul_zero]
  · have hr0 : y-x ≠ 0 := sub_ne_zero.mpr he
    have hγ : Values.vfValueHom (y-x) ≠ Values.infinity := by
      intro h
      have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (y-x))).mp h
      exact hr0 ((CanonicalRV.encodedRv_zero_iff (y-x)).mp hz)
    let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (y-x),hγ⟩
    have hαγ : α < γ := GammaDifferenceRealization.difference_gt_radius a α x y hx hy
    let g : Set.Ioi α := ⟨γ,hαγ⟩
    have hR := GammaTailShift.radius_ratio hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage g
    have hMap : valueMap a α f hfVF hinj g = (β/α)*γ := div_eq_iff_eq_mul.mp hR
    have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
    have hV := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj γ
      (coefficient a α f hfVF hinj g) (coefficient_spec a α f hfVF hinj g) x y hx hy rfl
    change Values.vfValueHom (fy-fx) = (valueMap a α f hfVF hinj g).val at hV
    calc
      Values.vfValueHom (fy-fx) = (valueMap a α f hfVF hinj g).val := hV
      _ = ((β/α)*γ).val := congrArg Subtype.val hMap
      _ = (β/α).val * γ.val := Values.gamma_val_mul _ _
      _ = (β/α).val * Values.vfValueHom (y-x) := rfl

theorem lemma_3_16 {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (hsmall : Cardinal.mk B.real < κ)
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (α β : Values.Gamma (M := M))
    (hRadA : PaperBalls.HasRadius A (↑α.val : PaperBalls.Radius (M := M)))
    (hRadImage : PaperBalls.HasRadius (f '' A) (↑β.val : PaperBalls.Radius (M := M))) :
    GammaLinear A f hfVF (β/α) := by
  rcases ho with hVF | ⟨a,σ,rfl⟩
  · have hAll : {x : M | iVF x} ⊆ A := hVF.symm ▸ Set.Subset.rfl
    exact (OpenBallConstancy.atomic_not_contains_vf B hA hAll).elim
  · have hRadσ : PaperBalls.HasRadius (gammaBall a σ true)
        (↑σ.val : PaperBalls.Radius (M := M)) := Or.inr (Or.inr ⟨a,σ,true,rfl,rfl⟩)
    have hσα : σ = α := Subtype.ext (WithBot.coe_inj.mp
      (PaperBallInvariants.hasRadius_unique δ hδ1 hRadσ hRadA))
    subst σ
    have hOpen : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
    obtain ⟨hImAtomic,hImOpen⟩ := RVInverse.atomic_open_image B h00 δ hδ hδ1 hOpen hA f hf hfVF hinj
    rcases hImOpen with hVF | ⟨b,τ,hImage⟩
    · have hAll : {x : M | iVF x} ⊆ f '' gammaBall a α true := hVF.symm ▸ Set.Subset.rfl
      exact (OpenBallConstancy.atomic_not_contains_vf B hImAtomic hAll).elim
    · have hRadτ : PaperBalls.HasRadius (f '' gammaBall a α true)
          (↑τ.val : PaperBalls.Radius (M := M)) := Or.inr (Or.inr ⟨b,τ,true,hImage,rfl⟩)
      have hτβ : τ = β := Subtype.ext (WithBot.coe_inj.mp
        (PaperBallInvariants.hasRadius_unique δ hδ1 hRadτ hRadImage))
      subst τ
      exact ordinary hκ hs B hsmall h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage

end IntegrationInACVF.Section3ACVF.GammaLinearity
