import IntegrationSection3ACVF.GammaSlopeOutput
import IntegrationSection3ACVF.InjectiveBallOrder

/-! The Gamma map on the source open tail, defined through the full
slope relation and proved to preserve strict order and target radii. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.GammaTailMap

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

noncomputable def coefficient (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) (γ : Set.Ioi α) : M :=
  Classical.choose ((GammaSlopeDomain.domain_iff a α γ.val f hfVF hinj).mpr γ.property)

noncomputable def valueMap (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) (γ : Set.Ioi α) : Values.Gamma (M := M) :=
  γ.val * codeValue (coefficient a α f hfVF hinj γ)

theorem coefficient_spec (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (f : M → M) (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x))
    (hinj : Set.InjOn f (gammaBall a α true)) (γ : Set.Ioi α) :
    RVSlopeGamma.relation (gammaBall a α true) f γ.val (coefficient a α f hfVF hinj γ) :=
  Classical.choose_spec ((GammaSlopeDomain.domain_iff a α γ.val f hfVF hinj).mpr γ.property)

private theorem from_centre (a : VFType (M := M)) (α γ : Values.Gamma (M := M)) (hαγ : α < γ) :
    ∃ y : VFType (M := M), y.val ∈ gammaBall a α true ∧ Values.vfValueHom (y-a) = γ.val := by
  obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
  have he : (a+r)-a = r := by ring
  have hv : Values.vfValueHom ((a+r)-a) = γ.val := (congrArg Values.vfValueHom he).trans hr
  refine ⟨a+r,?_,hv⟩
  change ∃ hy : iVF (a+r).val, α.val ≤ Values.vfValueHom ((a+r)-a) ∧
    (true = true → ¬ Values.vfValueHom ((a+r)-a) ≤ α.val)
  refine ⟨(a+r).property,hv.symm ▸ hαγ.le,?_⟩
  intro _ h
  have he : γ.val ≤ α.val := hv ▸ h
  exact not_le_of_gt hαγ he

theorem valueMap_mem (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true))
    (b : VFType (M := M)) (β : Values.Gamma (M := M))
    (hImage : f '' gammaBall a α true = gammaBall b β true) (γ : Set.Ioi α) :
    β < valueMap a α f hfVF hinj γ := by
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hx := BallEnlargementGeometry.gammaBall_centre_mem a α true
  obtain ⟨y,hy,hval⟩ := from_centre a α γ.val γ.property
  let fx : VFType (M := M) := ⟨f a.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  have hV := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    γ.val (coefficient a α f hfVF hinj γ) (coefficient_spec a α f hfVF hinj γ) a y hx hy hval
  change Values.vfValueHom (fy-fx) = (valueMap a α f hfVF hinj γ).val at hV
  have hfx : fx.val ∈ gammaBall b β true := (Set.ext_iff.mp hImage fx.val).mp ⟨a.val,hx,rfl⟩
  have hfy : fy.val ∈ gammaBall b β true := (Set.ext_iff.mp hImage fy.val).mp ⟨y.val,hy,rfl⟩
  have hl := GammaDifferenceRealization.difference_gt_radius b β fx fy hfx hfy
  have hβ : β.val < (valueMap a α f hfVF hinj γ).val := hV ▸ hl
  exact hβ

theorem strictMono (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (a : VFType (M := M)) (α : Values.Gamma (M := M))
    (hA : AdjoinBall.AtomicOver B (gammaBall a α true))
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn (gammaBall a α true) f))
    (hfVF : ∀ x ∈ gammaBall a α true, iVF (f x)) (hinj : Set.InjOn f (gammaBall a α true)) :
    StrictMono (valueMap a α f hfVF hinj) := by
  intro γ η hγη
  have ho : PaperBalls.IsOpenBall (gammaBall a α true) := Or.inr ⟨a,α,rfl⟩
  have hx := BallEnlargementGeometry.gammaBall_centre_mem a α true
  obtain ⟨y,hy,hγ⟩ := from_centre a α γ.val γ.property
  obtain ⟨z,hz,hη⟩ := from_centre a α η.val η.property
  let fx : VFType (M := M) := ⟨f a.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  let fz : VFType (M := M) := ⟨f z.val,hfVF _ hz⟩
  have hVγ := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    γ.val (coefficient a α f hfVF hinj γ) (coefficient_spec a α f hfVF hinj γ) a y hx hy hγ
  have hVη := GammaSlopeOutput.pair_output_value B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    η.val (coefficient a α f hfVF hinj η) (coefficient_spec a α f hfVF hinj η) a z hx hz hη
  change Values.vfValueHom (fy-fx) = (valueMap a α f hfVF hinj γ).val at hVγ
  change Values.vfValueHom (fz-fx) = (valueMap a α f hfVF hinj η).val at hVη
  have hdist : Values.vfValueHom (y-a) < Values.vfValueHom (z-a) := by
    have he : γ.val.val < η.val.val := hγη
    exact hγ.symm ▸ (hη.symm ▸ he)
  have hOut := InjectiveBallOrder.value_strictMono B h00 δ hδ hδ1 ho hA f hf hfVF hinj a y z hx hy hz hdist
  change Values.vfValueHom (fy-fx) < Values.vfValueHom (fz-fx) at hOut
  rw [hVγ,hVη] at hOut
  exact hOut

end IntegrationInACVF.Section3ACVF.GammaTailMap
