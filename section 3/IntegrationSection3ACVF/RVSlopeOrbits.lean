import IntegrationSection3ACVF.RVSlopeFibres
import IntegrationSection3ACVF.RVIntegerOrbits
import IntegrationSection3ACVF.RVSlopeFiniteCofinite

/-! Each nonempty fixed-coefficient slope fibre contains an infinite
integer orbit inside one actual Gamma value fibre. -/

set_option backward.isDefEq.respectTransparency false

open Set Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.RVDifferencePairs
open IntegrationInACVF.Section3ACVF.RVSlopeGraph

namespace IntegrationInACVF.Section3ACVF.RVSlopeOrbits

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem pair_orbit (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (x y : VFType (M := M)) (hx : x.val ∈ A) (hy : y.val ∈ A) (hne : y ≠ x) :
    ∃ c : CanonicalRV.RVSort M, ∀ n : ℕ,
      ![(CanonicalRV.encodedRv (((n+1 : ℕ) : VFType (M := M))*(y-x))).val,c.val] ∈ slopes A f := by
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
  have hc : NonzeroRV c.val :=
    ⟨c.property,fun h => (div_ne_zero hb0 hr0) ((CanonicalRV.encodedRv_zero_iff (b/r)).mp h)⟩
  refine ⟨c,fun n => ?_⟩
  let k := n+1
  have hk : k ≠ 0 := Nat.succ_ne_zero n
  let z := AffineHoleCosets.affine x y k
  have hz : z.val ∈ A := RVIntegerEquivariance.affine_mem h00 ho x y hx hy k
  have hzr : z-x = (k : VFType (M := M))*r := by dsimp [z,r,AffineHoleCosets.affine]; ring
  let t := CanonicalRV.encodedRv ((k : VFType (M := M))*r)
  have ht : NonzeroRV t.val :=
    ⟨t.property,fun h => (mul_ne_zero (Barycentre.natCast_ne_zero h00 k hk) hr0)
      ((CanonicalRV.encodedRv_zero_iff ((k : VFType (M := M))*r)).mp h)⟩
  have hinput : t.val = difference z.val x.val := by rw [difference_vf,hzr]; rfl
  have himage := RVIntegerEquivariance.integer_equivariance B h00 δ hδ hδ1 ho hA
    f hf hfVF hinj x y hx hy hne k hk
  have hkb : iRVMul (iRv (k : VFType (M := M)).val) (difference (f y.val) (f x.val)) =
      iRv ((k : VFType (M := M))*b).val := by
    have he := difference_vf fy fx
    exact (congrArg (iRVMul (iRv (k : VFType (M := M)).val)) he).trans
      (rv_mul_hom_of_model hM (k : VFType (M := M)).property b.property).symm
  have hcoef : multiply c.val t.val = iRv ((k : VFType (M := M))*b).val := by
    rw [multiply_rv c t]
    have he : (b/r)*((k : VFType (M := M))*r) = (k : VFType (M := M))*b := by
      field_simp [hr0]
    exact (rv_mul_hom_of_model hM (b/r).property ((k : VFType (M := M))*r).property).symm.trans
      (congrArg (fun u : VFType (M := M) => iRv u.val) he)
  have hout : multiply c.val t.val = difference (f z.val) (f x.val) :=
    hcoef.trans (himage.trans hkb).symm
  exact ⟨ht,hc,x.val,hx,z.val,hz,hinput,hout⟩

theorem infinite (B : FullBaseAtomicity.Base (M := M))
    (h00 : M ⊨ Axioms.ACVF00) (δ : Values.Gamma (M := M))
    (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    {A : Set M} (ho : PaperBalls.IsOpenBall A) (hA : AdjoinBall.AtomicOver B A)
    (f : M → M) (hf : FullBaseAtomicity.OverBase B (ImaginaryBaseImages.graphOn A f))
    (hfVF : ∀ x ∈ A, iVF (f x)) (hinj : Set.InjOn f A)
    (c : M) (γ : Values.Gamma (M := M))
    (hne : (Values.fibre (RVSlopeFiniteCofinite.row A f c) γ).Nonempty) :
    (Values.fibre (RVSlopeFiniteCofinite.row A f c) γ).Infinite := by
  obtain ⟨t,htγ,ht⟩ := hne
  have htSlope : ![t.val,c] ∈ slopes A f := ht
  obtain ⟨htNZ,_,x,hx,y,hy,htInput,_⟩ := htSlope
  have hAVF : A ⊆ {x | iVF x} := by
    rcases ho with h | ⟨a,β,h⟩
    · exact h ▸ Set.Subset.rfl
    · rw [h]
      intro u hu
      exact hu.1
  let xx : VFType (M := M) := ⟨x,hAVF hx⟩
  let yy : VFType (M := M) := ⟨y,hAVF hy⟩
  let r : VFType (M := M) := yy-xx
  have htRV : t = CanonicalRV.encodedRv r := Subtype.ext (htInput.trans (difference_vf yy xx))
  have hr0 : r ≠ 0 := by
    intro h
    exact htNZ.2 ((congrArg Subtype.val htRV).trans ((CanonicalRV.encodedRv_zero_iff r).mpr h))
  have hxy : yy ≠ xx := sub_ne_zero.mp hr0
  obtain ⟨d,hd⟩ := pair_orbit B h00 δ hδ hδ1 ho hA f hf hfVF hinj xx yy hx hy hxy
  have h0 : (CanonicalRV.encodedRv (((0+1 : ℕ) : VFType (M := M))*r)).val = t.val := by
    simpa only [Nat.zero_add,Nat.cast_one,one_mul] using (congrArg Subtype.val htRV).symm
  have hd0 : ![t.val,d.val] ∈ slopes A f := by
    have h := hd 0
    change ![(CanonicalRV.encodedRv (((0+1 : ℕ) : VFType (M := M))*r)).val,d.val] ∈ slopes A f at h
    rwa [h0] at h
  have hdc : d.val = c := RVSlopeFibres.unique B h00 δ hδ hδ1 ho hA f hf hfVF hinj hd0 ht
  have hrγ : Values.vfValueHom r = γ.val := (congrArg Values.vrv htRV).symm.trans htγ
  let orbit (n : ℕ) := CanonicalRV.encodedRv (((n+1 : ℕ) : VFType (M := M))*r)
  have hinf : (Set.range orbit).Infinite := Set.infinite_range_of_injective
    (RVIntegerOrbits.orbit_injective h00 r hr0)
  apply hinf.mono
  rintro u ⟨n,rfl⟩
  refine ⟨(RVIntegerOrbits.orbit_value h00 r n).trans hrγ,?_⟩
  change ![(orbit n).val,c] ∈ slopes A f
  rw [← hdc]
  exact hd n

end IntegrationInACVF.Section3ACVF.RVSlopeOrbits
