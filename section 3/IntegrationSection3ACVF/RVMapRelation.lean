import IntegrationSection3ACVF.RVPairConstancy
import IntegrationSection3ACVF.RVPairPreservation

/-! The common RV relation induced by an injective definable VF map on
an atomic open ball is single-valued, uniformly over all base points.
This establishes the RV-map step in the proof of Lemma 3.16. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs

namespace IntegrationInACVF.Section3ACVF.RVMapRelation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem difference_sorted (a b : M) (ha : iVF a) (hb : iVF b) :
    difference a b = iRv (iVFAdd a (iVFNeg b)) := by
  have h := difference_vf (⟨a,ha⟩ : VFType (M := M)) ⟨b,hb⟩
  rw [sub_eq_add_neg] at h
  exact h

theorem same_basepoint (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hBall : IsBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hz : z.val ∈ A)
    (he : difference z.val x.val = difference y.val x.val) :
    difference (f z.val) (f x.val) = difference (f y.val) (f x.val) := by
  have he' : iRv (z-x).val = iRv (y-x).val := by
    simpa only [difference_vf] using he
  rw [difference_sorted _ _ (hfVF _ hz) (hfVF _ hx),
    difference_sorted _ _ (hfVF _ hy) (hfVF _ hx)]
  exact RVPairPreservation.rv_difference B h00 δ hδ hδ1 hBall hA f hf hfVF hinj x y z hx hy hz he'

theorem right_unique (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z w : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hz : z.val ∈ A) (hw : w.val ∈ A)
    (he : difference y.val x.val = difference w.val z.val) :
    difference (f y.val) (f x.val) = difference (f w.val) (f z.val) := by
  have hBall : IsBall A := by
    rcases ho with h | ⟨a,γ,h⟩
    · exact Or.inl h
    · rw [h]
      exact BallEnlargementGeometry.gammaBall_isBall a γ true
  let t : Fin 2 → M := ![difference y.val x.val,difference (f y.val) (f x.val)]
  have ht : t ∈ RVPairConstancy.family A f x := ⟨y.val,hy,rfl,rfl⟩
  have hc := RVPairConstancy.constant B h00 δ hδ hδ1 ho hA f hf hfVF x hx z hz
  rw [hc] at ht
  obtain ⟨u,hu,hu1,hu2⟩ := ht
  have he' : difference u z.val = difference w.val z.val := hu1.symm.trans he
  have huVF : iVF u := by
    rcases ho with h | ⟨a,γ,h⟩
    · simpa only [h,Set.mem_ofPred_eq] using hu
    · rw [h] at hu
      exact hu.1
  have hr := same_basepoint B h00 δ hδ hδ1 hBall hA f hf hfVF hinj
    z w ⟨u,huVF⟩ hz hw hu he'
  exact hu2.trans hr

end IntegrationInACVF.Section3ACVF.RVMapRelation
