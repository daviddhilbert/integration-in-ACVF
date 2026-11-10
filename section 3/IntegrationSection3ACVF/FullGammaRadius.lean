import IntegrationSection3ACVF.FullBallCoset
import IntegrationSection3ACVF.GammaRadiusAtomicity

/-! Lemma 3.4 at an original-base definable actual Gamma radius. -/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity
open IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.FullGammaRadius

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem radiusTail_definable (B : FullBaseAtomicity.Base (M := M))
    (t : CanonicalRV.RVSort M) (strict : Bool)
    (hF : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ rvValuePullback (Values.vrv t)}) :
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ radiusTail t.val strict} := by
  let F := rvValuePullback (Values.vrv t)
  let T := radiusTail t.val strict
  let R : Set (M × M) :=
    {p | p.1 ∈ F ∧ iRV p.2 ∧ iLe p.1 p.2 ∧ (strict = true → ¬ iLe p.2 p.1)}
  have hf := hF
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .rv _).mp
    (@definableAt_sort M sM B.real .rv)).1
  have hnorm (u x : M) (hu : iRV u) (hx : iRV x) := rv_le_normalize u x hu hx
  have he : T = {x | ∃ u, (u,x) ∈ R} := by
    ext x
    constructor
    · rintro ⟨hx,hl,hr⟩
      exact ⟨t.val,⟨t.property,rfl⟩,hx,hl,hr⟩
    · rintro ⟨u,⟨hu,huv⟩,hx,hl,hr⟩
      have hl' : iLe u x ↔ iLe t.val x := by
        rw [← Values.vrv_le_iff ⟨u,hu⟩ ⟨x,hx⟩,huv,Values.vrv_le_iff]
      have hr' : iLe x u ↔ iLe x t.val := by
        rw [← Values.vrv_le_iff ⟨x,hx⟩ ⟨u,hu⟩,huv,Values.vrv_le_iff]
      exact ⟨hx,hl'.mp hl,fun ho h => hr ho (hr'.mpr h)⟩
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have h0 := ImaginaryParameters.OverBase.preimage_comp hf (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs).preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
  have hl := GammaParameters.raw_le_definable (M := M) B.real
  have hl := ImaginaryParameters.OverBase.of_real (p := p) (B := B) hl
  have hr := hl.preimage_comp (![1,0] : Fin 2 → Fin 2)
  have hR : ImaginaryParameters.OverBase (L := LRV) p B {z : Fin 2 → M | (z 0,z 1) ∈ R} := by
    change ImaginaryParameters.OverBase (L := LRV) p B {z : Fin 2 → M | (z 0,z 1) ∈ R}
    cases strict with
    | false =>
      convert ImaginaryParameters.OverBase.inter h0
        (ImaginaryParameters.OverBase.inter h1 hl hp) hp using 1
      ext z
      change (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M sM (z 0) (z 1) ∧
        (false = true → ¬ @iLe M sM (z 1) (z 0))) ↔
        (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M N (z 0) (z 1))
      simp only [Bool.false_eq_true,false_implies,and_true]
      exact and_congr_right fun hu => and_congr_right fun hx =>
        (hnorm _ _ hu.choose hx).symm
    | true =>
      convert ImaginaryParameters.OverBase.inter h0
        (ImaginaryParameters.OverBase.inter h1
          (ImaginaryParameters.OverBase.inter hl (ImaginaryParameters.OverBase.compl hr hp) hp) hp) hp using 1
      ext z
      change (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M sM (z 0) (z 1) ∧
        (true = true → ¬ @iLe M sM (z 1) (z 0))) ↔
        (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M N (z 0) (z 1) ∧
          ¬ @iLe M N (z 1) (z 0))
      simp only [true_implies]
      exact and_congr_right fun hu => and_congr_right fun hx =>
        and_congr (hnorm _ _ hu.choose hx).symm
          (not_congr (hnorm _ _ hx hu.choose).symm)
  have hd := ImaginaryParameters.OverBase.exists_block
    (hR.preimage_comp (![Sum.inr 0,Sum.inl 0] : Fin 2 → Fin 1 ⊕ Fin 1))
  change ImaginaryParameters.OverBase (L := LRV) p B {z : Fin 1 → M | z 0 ∈ T}
  rw [he]
  convert hd using 1
  ext z
  exact ⟨fun ⟨u,hu⟩ => ⟨![u],hu⟩,fun ⟨u,hu⟩ => ⟨u 0,hu⟩⟩


theorem rv_preimage {B : FullBaseAtomicity.Base (M := M)} {T : Set M}
    (hT : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ T}) :
    FullBaseAtomicity.OverBase B {z : Fin 1 → M | iVF (z 0) ∧ iRv (z 0) ∈ T} := by
  have hs := ((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
    (@definableAt_sort M sM B.real .vf)).1
  have hnorm (x : M) (hx : iVF x) :
      @iRv M (CanonicalStructure.normalize (M := M)) x = @iRv M sM x :=
    CanonicalStructure.normalize_fun Fn.rvMap ![x] (fun j => by fin_cases j; exact hx)
  let U : Set (Fin 1 → M) := {z | iVF (z 0) ∧ iRv (z 0) ∈ T}
  have hp := ParameterPresentation.codeDomain_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hr : B.real.DefinableFun LRV (fun z : Fin 1 → M => iRv (z 0)) := by
    have hf : B.real.DefinableFun LRV (Structure.funMap (L := LRV) Fn.rvMap) :=
      Set.DefinableFun.of_empty (@Set.DefinableFun.fun_symbol M LRV N 1 Fn.rvMap)
    exact hf.comp (fun j => by fin_cases j; exact Set.DefinableFun.proj LRV)
  have hd := ImaginaryParameters.OverBase.inter
    (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hs)
    (ImaginaryParameters.OverBase.preimage_map hT (fun _ : Fin 1 => hr)) hp
  change ImaginaryParameters.OverBase (L := LRV) p B U
  convert hd using 1
  ext z
  change (@iVF M sM (z 0) ∧ @iRv M sM (z 0) ∈ T) ↔
    (@iVF M sM (z 0) ∧ @iRv M N (z 0) ∈ T)
  exact and_congr_right (fun hx => by rw [hnorm _ hx])

theorem radius_subgroup (B : FullBaseAtomicity.Base (M := M))
    (t : CanonicalRV.RVSort M) (ht0 : t.val ≠ iRVZero) (strict : Bool)
    (hT : FullBaseAtomicity.OverBase B {z : Fin 1 → M | z 0 ∈ radiusTail t.val strict}) :
    ∃ H : AddSubgroup (VFType (M := M)),
      FullBaseAtomicity.OverBase B
        {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))} ∧
      ∀ a : VFType (M := M), cosetBody H a = radiusBall a t.val strict := by
  obtain ⟨H,_,he⟩ := NamedRadiusAtomicity.radius_subgroup Set.univ t.val t.property ht0 strict
    (NamedRadiusAtomicity.radiusTail_definable Set.univ t.val t.property (Set.mem_univ _) strict)
  have hz : Subtype.val '' (H : Set (VFType (M := M))) =
      {x | iVF x ∧ iRv x ∈ radiusTail t.val strict} := by
    ext x
    have hd (hx : iVF x) : iVFAdd x (iVFNeg (0 : VFType (M := M)).val) = x := by
      let u : VFType (M := M) := ⟨x,hx⟩
      change (u + -0).val = x
      simp only [neg_zero,add_zero]
      rfl
    constructor
    · rintro ⟨u,hu,rfl⟩
      change u ∈ H at hu
      have hus : u - 0 ∈ H := by rw [sub_zero]; exact hu
      have hc : u.val ∈ cosetBody H 0 :=
        ⟨u,QuotientAddGroup.eq_iff_sub_mem.mpr hus,rfl⟩
      rw [he 0] at hc
      change iVF u.val ∧ iLe t.val (iRv (iVFAdd u.val (iVFNeg (0 : VFType (M := M)).val))) ∧
        (strict = true → ¬ iLe (iRv (iVFAdd u.val (iVFNeg (0 : VFType (M := M)).val))) t.val) at hc
      rw [hd u.property] at hc
      exact ⟨u.property,rv_mem hM u.property,hc.2⟩
    · rintro ⟨hx,hr⟩
      let u : VFType (M := M) := ⟨x,hx⟩
      have hc : x ∈ radiusBall 0 t.val strict := by
        change iVF x ∧ iLe t.val (iRv (iVFAdd x (iVFNeg (0 : VFType (M := M)).val))) ∧ _
        rw [hd hx]
        exact ⟨hx,hr.2⟩
      rw [← he 0] at hc
      obtain ⟨v,hv,hvx⟩ := hc
      have hvu : v = u := Subtype.ext hvx
      rw [hvu] at hv
      have hus : u - 0 ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hv
      rw [sub_zero] at hus
      exact ⟨u,hus,rfl⟩
  refine ⟨H,?_,he⟩
  have hr := rv_preimage hT
  convert hr using 1
  ext z
  exact Set.ext_iff.mp hz (z 0)

theorem lemma_3_4 (B : FullBaseAtomicity.Base (M := M))
    (γ : Values.Gamma (M := M)) (hγ : FullGammaSyntax.Scalar B {γ})
    (strict : Bool) {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (a : VFType (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a γ strict)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  obtain ⟨t,ht0,htγ⟩ := Values.gamma_has_nonzero_representative γ
  have hv : rvValuePullback (Values.vrv t) = Values.gammaPullback {γ} := by
    rw [htγ]
    ext x
    constructor
    · rintro ⟨hx,he⟩
      have hx0 : x ≠ iRVZero := by
        intro hz
        exact γ.property (he.symm.trans ((Values.vrv_eq_infinity_iff _).mpr hz))
      exact ⟨hx,hx0,Subtype.ext he⟩
    · rintro ⟨hx,hx0,he⟩
      exact ⟨hx,congrArg Subtype.val he⟩
  have hF : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ rvValuePullback (Values.vrv t)} := by
    rw [hv]
    exact hγ
  obtain ⟨H,hH,he⟩ := radius_subgroup B t ht0 strict (radiusTail_definable B t strict hF)
  have hi' := hi.trans (radiusBall_eq_gammaBall a t γ htγ strict).symm
  exact FullBallCoset.atomicWith_to_adjoin B i _
    (FullBallCoset.atomic_coset B H hH hA i ⟨a,hi'.trans (he a).symm⟩ hsub)


theorem lemma_3_4_singleton (B : FullBaseAtomicity.Base (M := M))
    (i : BallImaginaries.Ball M) (hi : (BallImaginaries.underlying i).Subsingleton) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  have hm := BallPresentation.membership_definable (M := M) B.real
  let p := @ParameterPresentation.presentation M sM hM
  have hat : FullBaseAtomicity.AtomicWith B i (BallImaginaries.underlying i) := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryBaseFamilies.atomicWith_of_subsingleton
      (ImaginaryParameters.OverBase.of_real (p := p) (B := B) hm) i hi
  exact FullBallCoset.atomicWith_to_adjoin B i _ hat

theorem lemma_3_4_whole_field (B : FullBaseAtomicity.Base (M := M))
    {A : Set M} (hA : FullBallCoset.CompleteType B A)
    (i : BallImaginaries.Ball M) (hi : BallImaginaries.underlying i = {x | iVF x})
    (hsub : BallImaginaries.underlying i ⊆ A) :
    AdjoinBall.AtomicOver (B.adjoin (Sum.inl i)) (BallImaginaries.underlying i) := by
  let H : AddSubgroup (VFType (M := M)) := ⊤
  have he : Subtype.val '' (H : Set (VFType (M := M))) = {x | iVF x} := by
    ext x
    exact ⟨fun ⟨u,_,hu⟩ => hu ▸ u.property,fun hx => ⟨⟨x,hx⟩,trivial,rfl⟩⟩
  have hH : FullBaseAtomicity.OverBase B
      {z : Fin 1 → M | z 0 ∈ Subtype.val '' (H : Set (VFType (M := M)))} := by
    rw [he]
    exact FullBaseAtomicity.OverBase.of_real (B := B)
      (((@definableAt_iff_normalized_raw M sM hM B.real .vf _).mp
        (@definableAt_sort M sM B.real .vf)).1)
  have hc : cosetBody H (0 : VFType (M := M)) = {x | iVF x} := by
    ext x
    constructor
    · rintro ⟨u,_,rfl⟩
      exact u.property
    · intro hx
      let u : VFType (M := M) := ⟨x,hx⟩
      refine ⟨u,?_,rfl⟩
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (show u-0 ∈ H from trivial)
  exact FullBallCoset.atomicWith_to_adjoin B i _
    (FullBallCoset.atomic_coset B H hH hA i ⟨0,hi.trans hc.symm⟩ hsub)


end IntegrationInACVF.Section3ACVF.FullGammaRadius
