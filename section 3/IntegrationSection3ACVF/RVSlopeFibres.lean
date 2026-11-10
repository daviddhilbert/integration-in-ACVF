import IntegrationSection3ACVF.RVSlopeGraph
import IntegrationSection3ACVF.RVInputFibre
import IntegrationSection3ACVF.RVIntegerEquivariance

/-! Existence and uniqueness of actual RV slope coefficients on the
common difference relation of an injective map on an atomic open ball. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.RVSlopeFibres

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem slope_of_pair {A : Set M} (f : M → M) (hfVF : ∀ x ∈ A, iVF (f x))
    (hinj : Set.InjOn f A) (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A)
    (hne : y ≠ x) : ∃ c : CanonicalRV.RVSort M,
      ![difference y.val x.val,c.val] ∈ slopes A f := by
  let r : VFType (M := M) := y-x
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  let b : VFType (M := M) := fy-fx
  have hr0 : r ≠ 0 := sub_ne_zero.mpr hne
  have hb0 : b ≠ 0 := by
    intro h
    have he : fy = fx := sub_eq_zero.mp h
    exact hne (Subtype.ext (hinj hy hx (congrArg Subtype.val he)))
  let c := CanonicalRV.encodedRv (b/r)
  have ht : NonzeroRV (difference y.val x.val) := by
    rw [difference_vf]
    exact ⟨rv_mem hM r.property,fun h => hr0 ((CanonicalRV.encodedRv_zero_iff r).mp h)⟩
  have hc : NonzeroRV c.val :=
    ⟨c.property,fun h => (div_ne_zero hb0 hr0) ((CanonicalRV.encodedRv_zero_iff (b/r)).mp h)⟩
  have hm : multiply c.val (difference y.val x.val) = difference (f y.val) (f x.val) := by
    rw [difference_vf]
    change multiply c.val (CanonicalRV.encodedRv r).val = difference (f y.val) (f x.val)
    rw [multiply_rv c (CanonicalRV.encodedRv r)]
    have hp : (b/r)*r = b := div_mul_cancel₀ b hr0
    have hmul : iRVMul c.val (iRv r.val) = iRv b.val := by
      exact (rv_mul_hom_of_model hM (b/r).property r.property).symm.trans
        (congrArg (fun z : VFType (M := M) => iRv z.val) hp)
    exact hmul.trans (difference_vf fy fx).symm
  exact ⟨c,ht,hc,x.val,hx,y.val,hy,rfl,hm⟩

theorem unique (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    {t c d : M} (hc : ![t,c] ∈ slopes A f) (hd : ![t,d] ∈ slopes A f) : c = d := by
  obtain ⟨ht,hc,x,hx,y,hy,ht1,hu1⟩ := hc
  obtain ⟨_,hd,z,hz,w,hw,ht2,hu2⟩ := hd
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with h | ⟨a,γ,h⟩
    · exact h ▸ Set.Subset.rfl
    · rw [h]
      intro u hu
      exact hu.1
  have he := RVMapRelation.right_unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj
    ⟨x,hAVF hx⟩ ⟨y,hAVF hy⟩ ⟨z,hAVF hz⟩ ⟨w,hAVF hw⟩ hx hy hz hw
    (ht1.symm.trans ht2)
  have hm : multiply c t = multiply d t := hu1.trans (he.trans hu2.symm)
  rw [multiply_rv (⟨c,hc.1⟩ : CanonicalRV.RVSort M) ⟨t,ht.1⟩,
    multiply_rv (⟨d,hd.1⟩ : CanonicalRV.RVSort M) ⟨t,ht.1⟩] at hm
  exact rv_mul_left_cancel_of_model hM hc.1 ht.1 ht.2 hd.1 hm

end IntegrationInACVF.Section3ACVF.RVSlopeFibres
