import IntegrationSection3ACVF.OpenSubballImages
import IntegrationSection3ACVF.RVFibreSubballs

/-! Injective definable VF maps on a definable atomic ball respect RV
classes of differences at each fixed base point. Arbitrary original
real, Gamma and ball names are retained. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3

open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF.RVPairPreservation

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem rv_difference (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (hBall : IsBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y z : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hz : z.val ∈ A)
    (he : iRv (z-x).val = iRv (y-x).val) :
    iRv (iVFAdd (f z.val) (iVFNeg (f x.val))) =
      iRv (iVFAdd (f y.val) (iVFNeg (f x.val))) := by
  by_cases hne : y = x
  · have hzx : z = x := by
      apply sub_eq_zero.mp
      exact (CanonicalRV.encodedRv_zero_iff (z-x)).mp
        (he.trans ((CanonicalRV.encodedRv_zero_iff (y-x)).mpr (sub_eq_zero.mpr hne)))
    subst y
    subst z
    rfl
  · obtain ⟨i,hi,hsub,hyi,hzi,hxi⟩ := RVFibreSubballs.exists_subball hBall x y z hx hy hne he
    have hImage := OpenSubballImages.image_open_of_atomic B h00 δ hδ hδ1 hA f hf hfVF hinj i hi hsub
    have hxImage : f x.val ∉ f '' BallImaginaries.underlying i := by
      rintro ⟨u,hu,heq⟩
      exact hxi ((hinj (hsub hu) hx heq) ▸ hu)
    have hc := OpenBallRVGeometry.rv_sub_constant hImage
      ⟨f x.val,hfVF _ hx⟩ ⟨f z.val,hfVF _ hz⟩ ⟨f y.val,hfVF _ hy⟩ hxImage
      ⟨z.val,hzi,rfl⟩ ⟨y.val,hyi,rfl⟩
    rw [sub_eq_add_neg,sub_eq_add_neg] at hc
    change iRv (iVFAdd (f z.val) (iVFNeg (f x.val))) =
      iRv (iVFAdd (f y.val) (iVFNeg (f x.val))) at hc
    exact hc

end IntegrationInACVF.Section3ACVF.RVPairPreservation
