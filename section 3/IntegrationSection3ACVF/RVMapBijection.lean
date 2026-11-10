import IntegrationSection3ACVF.RVMapRelation
import IntegrationSection3ACVF.RVInverse

/-! The difference relation of an injective definable VF map on an
atomic open ball preserves and reflects equality of RV classes, even
when the two pairs have different base points. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace IntegrationInACVF.Section3ACVF.RVMapBijection

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem left_unique (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z w : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hz : z.val ∈ A) (hw : w.val ∈ A)
    (he : difference (f y.val) (f x.val) = difference (f w.val) (f z.val)) :
    difference y.val x.val = difference w.val z.val := by
  obtain ⟨hImage,hImageOpen⟩ := RVInverse.atomic_open_image B h00 δ hδ hδ1 ho hA f hf hfVF hinj
  let g := RVInverse.inverse A f
  have hgraph := RVInverse.inverse_graph_definable B hinj hf
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with h | ⟨a,γ,h⟩
    · exact h ▸ Set.Subset.rfl
    · rw [h]
      intro u hu
      exact hu.1
  have hgVF (u : M) (hu : u ∈ f '' A) : iVF (g u) :=
    hAVF (RVInverse.inverse_right hu).1
  have hgi : Set.InjOn g (f '' A) := RVInverse.inverse_injOn A f
  have hr := RVMapRelation.right_unique B h00 δ hδ hδ1 hImageOpen hImage g hgraph hgVF hgi
    ⟨f x.val,hfVF _ hx⟩ ⟨f y.val,hfVF _ hy⟩ ⟨f z.val,hfVF _ hz⟩ ⟨f w.val,hfVF _ hw⟩
    ⟨x.val,hx,rfl⟩ ⟨y.val,hy,rfl⟩ ⟨z.val,hz,rfl⟩ ⟨w.val,hw,rfl⟩ he
  simpa only [g,RVInverse.inverse_on hinj hx,RVInverse.inverse_on hinj hy,
    RVInverse.inverse_on hinj hz,RVInverse.inverse_on hinj hw] using hr

theorem difference_iff (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z w : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hz : z.val ∈ A) (hw : w.val ∈ A) :
    difference y.val x.val = difference w.val z.val ↔
      difference (f y.val) (f x.val) = difference (f w.val) (f z.val) :=
  ⟨RVMapRelation.right_unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj x y z w hx hy hz hw,
    left_unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj x y z w hx hy hz hw⟩

end IntegrationInACVF.Section3ACVF.RVMapBijection
