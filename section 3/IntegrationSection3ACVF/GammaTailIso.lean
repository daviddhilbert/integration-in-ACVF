import IntegrationSection3ACVF.GammaTailMap

/-! The valuation map induced by the definable injection is an order
isomorphism between the source and image open Gamma tails. Surjectivity
comes from lifting two actual image points, not from an assumed value map. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.GammaTailMap

namespace IntegrationInACVF.Section3ACVF.GammaTailIso

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem surjective (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) (η : Set.Ioi β) :
    ∃ γ : Set.Ioi α, valueMap a α f hfVF hinj γ = η.val := by
  obtain ⟨p,q,hp,hq,hne,hη⟩ := GammaDifferenceRealization.exists_pair b β η.val η.property
  obtain ⟨x,hx,hfx⟩ := (Set.ext_iff.mp hImage p.val).mpr hp
  obtain ⟨y,hy,hfy⟩ := (Set.ext_iff.mp hImage q.val).mpr hq
  let xx : VFType (M := M) := ⟨x,hx.1⟩
  let yy : VFType (M := M) := ⟨y,hy.1⟩
  have hxy : yy ≠ xx := by
    intro he
    have hfEq : f y = f x := congrArg f (congrArg Subtype.val he)
    exact hne (Subtype.ext (hfy.symm.trans (hfEq.trans hfx)))
  have hr0 : yy-xx ≠ 0 := sub_ne_zero.mpr hxy
  have hγ : Values.vfValueHom (yy-xx) ≠ Values.infinity := by
    intro h
    have hz := (Values.vrv_eq_infinity_iff (CanonicalRV.encodedRv (yy-xx))).mp h
    exact hr0 ((CanonicalRV.encodedRv_zero_iff (yy-xx)).mp hz)
  let γ : Values.Gamma (M := M) := ⟨Values.vfValueHom (yy-xx),hγ⟩
  have hαγ : α < γ := GammaDifferenceRealization.difference_gt_radius a α xx yy hx hy
  let g : Set.Ioi α := ⟨γ,hαγ⟩
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  let fx : VFType (M := M) := ⟨f x,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y,hfVF _ hy⟩
  have hV := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    γ (coefficient a α f hfVF hinj g) (coefficient_spec a α f hfVF hinj g) xx yy hx hy rfl
  change Values.vfValueHom (fy-fx) = (valueMap a α f hfVF hinj g).val at hV
  have hxEq : fx = p := Subtype.ext hfx
  have hyEq : fy = q := Subtype.ext hfy
  rw [hxEq,hyEq] at hV
  exact ⟨g,Subtype.ext (hV.symm.trans hη)⟩

noncomputable def orderIso (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) : Set.Ioi α ≃o Set.Ioi β := by
  let g : Set.Ioi α → Set.Ioi β := fun γ => ⟨valueMap a α f hfVF hinj γ,
    valueMap_mem B h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage γ⟩
  have hStrict : StrictMono g := fun _ _ h =>
    GammaTailMap.strictMono B h00 δ hδ hδ1 a α hA f hf hfVF hinj h
  have hSurj : Function.Surjective g := by
    intro η
    obtain ⟨γ,hγ⟩ := surjective B h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage η
    exact ⟨γ,Subtype.ext hγ⟩
  exact { toEquiv := Equiv.ofBijective g ⟨hStrict.injective,hSurj⟩
          map_rel_iff' := hStrict.le_iff_le }

theorem orderIso_val (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) (γ : Set.Ioi α) :
    (orderIso B h00 δ hδ hδ1 a α hA f hf hfVF hinj b β hImage γ).val = valueMap a α f hfVF hinj γ := rfl

end IntegrationInACVF.Section3ACVF.GammaTailIso
