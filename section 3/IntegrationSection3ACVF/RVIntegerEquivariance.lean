import IntegrationSection3ACVF.RVMapBijection
import IntegrationSection3ACVF.RVIntegerSequences

/-! Integer equivariance of the common RV difference relation. Neither
centres nor lifts of radii are added to the original parameter base. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.RVIntegerEquivariance

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem affine_mem (h00 : M ⊨ Axioms.ACVF00) {A : Set M} (ho : PaperBalls.IsOpenBall A)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (n : ℕ) :
    (AffineHoleCosets.affine x y n).val ∈ A := by
  rcases ho with h | ⟨a,γ,h⟩
  · exact h.symm ▸ (AffineHoleCosets.affine x y n).property
  · rw [h] at hx hy ⊢
    obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
    letI := hΓ
    obtain ⟨r,hr⟩ := GammaCosetGeometry.vf_representative γ
    apply (GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr _).mpr
    exact ValuationProgressions.affine_mem_open v (GammaCosetGeometry.valuation_nat_unit h00 v hv)
      a x y (v r)
      ((GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr x).mp hx)
      ((GammaCosetGeometry.gammaBall_mem_valuation v hv a r γ hr y).mp hy) n

theorem integer_equivariance (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hne : y ≠ x)
    (n : ℕ) (hn : n ≠ 0) :
    difference (f (AffineHoleCosets.affine x y n).val) (f x.val) =
      iRVMul (iRv (n : VFType (M := M)).val) (difference (f y.val) (f x.val)) := by
  let p := AffineHoleCosets.affine x y
  have hp (j : ℕ) : (p j).val ∈ A := affine_mem h00 ho x y hx hy j
  let g (j : ℕ) : VFType (M := M) := ⟨f (p j).val,hfVF _ (hp j)⟩
  let fx : VFType (M := M) := ⟨f x.val,hfVF _ hx⟩
  let fy : VFType (M := M) := ⟨f y.val,hfVF _ hy⟩
  let b : VFType (M := M) := fy-fx
  have hb : b ≠ 0 := by
    intro h
    have he : fy = fx := sub_eq_zero.mp h
    exact hne (Subtype.ext (hinj hy hx (congrArg Subtype.val he)))
  have hstep (j : ℕ) : iRv (g (j+1)-g j).val = iRv b.val := by
    have hs : p (j+1)-p j = y-x := by
      dsimp [p,AffineHoleCosets.affine]
      rw [Nat.cast_add,Nat.cast_one]
      ring
    have he : difference y.val x.val = difference (p (j+1)).val (p j).val := by
      rw [difference_vf,difference_vf,hs]
    have hr := RVMapRelation.right_unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj
      x y (p j) (p (j+1)) hx hy (hp j) (hp (j+1)) he
    have hl : difference (f y.val) (f x.val) = iRv b.val := difference_vf fy fx
    have hh : difference (f (p (j+1)).val) (f (p j).val) = iRv (g (j+1)-g j).val :=
      difference_vf (g (j+1)) (g j)
    rw [hl,hh] at hr
    exact hr.symm
  have hs := RVIntegerSequences.sequence_rv h00 g b hb hstep n hn
  rw [← difference_vf (g n) (g 0)] at hs
  have hp0 : p 0 = x := by simp [p,AffineHoleCosets.affine]
  change difference (f (p n).val) (f (p 0).val) = iRv ((n : VFType (M := M))*b).val at hs
  rw [hp0] at hs
  have hm : iRv ((n : VFType (M := M))*b).val =
      iRVMul (iRv (n : VFType (M := M)).val) (iRv b.val) :=
    rv_mul_hom_of_model hM (n : VFType (M := M)).property b.property
  exact hs.trans (hm.trans (congrArg (iRVMul (iRv (n : VFType (M := M)).val))
    (difference_vf fy fx).symm))

end IntegrationInACVF.Section3ACVF.RVIntegerEquivariance
