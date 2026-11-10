import IntegrationSection3ACVF.NamedRadiusAtomicity

/-!
# Definable Gamma radii

The radius is a point of the existing value-group quotient. Its entire RV
value fibre is quantified, so neither an RV lift nor a VF lift is named.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity
open IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity

namespace IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A definable value fibre suffices; a particular RV representative need
not be in the parameter base. -/
theorem radiusTail_definable_of_value (Q : Set M) (t : CanonicalRV.RVSort M)
    (strict : Bool) (hF : RVValueDefinable Q (Values.vrv t)) :
    DefinableAt Q .rv (radiusTail t.val strict) := by
  let F := rvValuePullback (Values.vrv t)
  let T := radiusTail t.val strict
  let R : Set (M × M) :=
    {p | p.1 ∈ F ∧ iRV p.2 ∧ iLe p.1 p.2 ∧ (strict = true → ¬ iLe p.2 p.1)}
  have hf := ((@definableAt_iff_normalized_raw M sM hM Q .rv _).mp hF).1
  have hs := ((@definableAt_iff_normalized_raw M sM hM Q .rv _).mp
    (@definableAt_sort M sM Q .rv)).1
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
  apply (@definableAt_iff_normalized_raw M sM hM Q .rv T).mpr
  refine ⟨?_,fun _ hx => hx.1⟩
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have h0 := hf.preimage_comp (fun _ : Fin 1 => (0 : Fin 2))
  have h1 := hs.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
  have hl := GammaParameters.raw_le_definable (M := M) Q
  have hr := hl.preimage_comp (![1,0] : Fin 2 → Fin 2)
  have hR : Q.Definable₂ LRV R := by
    change Q.Definable LRV {z : Fin 2 → M | (z 0,z 1) ∈ R}
    cases strict with
    | false =>
      convert h0.inter (h1.inter hl) using 1
      ext z
      change (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M sM (z 0) (z 1) ∧
        (false = true → ¬ @iLe M sM (z 1) (z 0))) ↔
        (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M N (z 0) (z 1))
      simp only [Bool.false_eq_true,false_implies,and_true]
      exact and_congr_right fun hu => and_congr_right fun hx =>
        (hnorm _ _ hu.choose hx).symm
    | true =>
      convert h0.inter (h1.inter (hl.inter hr.compl)) using 1
      ext z
      change (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M sM (z 0) (z 1) ∧
        (true = true → ¬ @iLe M sM (z 1) (z 0))) ↔
        (z 0 ∈ F ∧ @iRV M sM (z 1) ∧ @iLe M N (z 0) (z 1) ∧
          ¬ @iLe M N (z 1) (z 0))
      simp only [true_implies]
      exact and_congr_right fun hu => and_congr_right fun hx =>
        and_congr (hnorm _ _ hu.choose hx).symm
          (not_congr (hnorm _ _ hx hu.choose).symm)
  rw [he]
  exact definable_range hR

private noncomputable def difference (x y : VFType (M := M)) : VFType (M := M) := x-y

/-- A ball written using the actual Gamma value, in the paper's order. -/
def gammaBall (a : VFType (M := M)) (γ : Values.Gamma (M := M))
    (strict : Bool) : Set M :=
  {x | ∃ hx : iVF x,
    γ.val ≤ (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) ∧
      (strict = true → ¬ (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) ≤ γ.val)}

theorem radiusBall_eq_gammaBall (a : VFType (M := M)) (t : CanonicalRV.RVSort M)
    (γ : Values.Gamma (M := M)) (htγ : Values.vrv t = γ.val) (strict : Bool) :
    radiusBall a t.val strict = gammaBall a γ strict := by
  ext x
  have hc (hx : iVF x) :
      iLe t.val (iRv (iVFAdd x (iVFNeg a.val))) ↔
        γ.val ≤ (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) := by
    let u : VFType (M := M) := ⟨x,hx⟩
    have hd : (u-a).val = iVFAdd x (iVFNeg a.val) := by
      rw [sub_eq_add_neg]; rfl
    have h := Values.vrv_le_iff t (CanonicalRV.encodedRv (u-a))
    change Values.vrv t ≤ (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) ↔ _ at h
    rw [htγ,hd] at h
    exact h.symm
  have hc' (hx : iVF x) :
      iLe (iRv (iVFAdd x (iVFNeg a.val))) t.val ↔
        (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) ≤ γ.val := by
    let u : VFType (M := M) := ⟨x,hx⟩
    have hd : (u-a).val = iVFAdd x (iVFNeg a.val) := by
      rw [sub_eq_add_neg]; rfl
    have h := Values.vrv_le_iff (CanonicalRV.encodedRv (u-a)) t
    change (@Values.vfValueHom M sM hM) (difference ⟨x,hx⟩ a) ≤ Values.vrv t ↔ _ at h
    rw [htγ,hd] at h
    exact h.symm
  constructor
  · rintro ⟨hx,hl,hr⟩
    exact ⟨hx,(hc hx).mp hl,fun ho h => hr ho ((hc' hx).mpr h)⟩
  · rintro ⟨hx,hl,hr⟩
    exact ⟨hx,(hc hx).mpr hl,fun ho h => hr ho ((hc' hx).mp h)⟩

/-- Lemma 3.4 over a real base, with any ordinary radius definable over that
base in the genuine Gamma sort. No radius representative is a parameter. -/
theorem lemma_3_4_real_base (Q : Set M) (γ : Values.Gamma (M := M))
    (hγ : Values.GammaDefinable Q {γ}) (strict : Bool) {A : Set M}
    (hA : @GeneratesCompleteType LRV M (CanonicalStructure.normalize (M := M)) (Fin 1) Q
      {z | z 0 ∈ A})
    (i : BallImaginaries.Ball M) (a : VFType (M := M))
    (hi : BallImaginaries.underlying i = gammaBall a γ strict)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q i
      (BallImaginaries.underlying i) := by
  obtain ⟨t,ht0,htγ⟩ := Values.gamma_has_nonzero_representative γ
  have hF : RVValueDefinable Q (Values.vrv t) := by
    rw [htγ]
    exact gamma_value_definable γ hγ
  obtain ⟨H,hH,he⟩ := radius_subgroup Q t.val t.property ht0 strict
    (radiusTail_definable_of_value Q t strict hF)
  have hi' := hi.trans (radiusBall_eq_gammaBall a t γ htγ strict).symm
  exact atomic_ball_coset_below_complete_type Q H hH hA i
    ⟨a,hi'.trans (he a).symm⟩ hsub

/-- The singleton degeneracy is atomic over its ball name over every real
base, without a hypothesis on an ambient type. -/
theorem lemma_3_4_singleton (Q : Set M) (i : BallImaginaries.Ball M)
    (hi : (BallImaginaries.underlying i).Subsingleton) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q i
      (BallImaginaries.underlying i) := by
  have hm := BallPresentation.membership_definable (M := M) Q
  letI := CanonicalStructure.normalize (M := M)
  exact atomicWith_of_subsingleton hm i hi

/-- The whole VF sort is the coset of its full additive subgroup. -/
theorem lemma_3_4_whole_field (Q : Set M) {A : Set M}
    (hA : @GeneratesCompleteType LRV M (CanonicalStructure.normalize (M := M)) (Fin 1) Q
      {z | z 0 ∈ A})
    (i : BallImaginaries.Ball M) (hi : BallImaginaries.underlying i = {x | iVF x})
    (hsub : BallImaginaries.underlying i ⊆ A) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q i
      (BallImaginaries.underlying i) := by
  let H : AddSubgroup (VFType (M := M)) := ⊤
  have he : Subtype.val '' (H : Set (VFType (M := M))) = {x | iVF x} := by
    ext x
    exact ⟨fun ⟨u,_,hu⟩ => hu ▸ u.property,fun hx => ⟨⟨x,hx⟩,trivial,rfl⟩⟩
  have hH : DefinableAt Q .vf (Subtype.val '' (H : Set (VFType (M := M)))) :=
    he.symm ▸ definableAt_sort Q .vf
  have hc : cosetBody H (0 : VFType (M := M)) = {x | iVF x} := by
    ext x
    constructor
    · rintro ⟨u,_,rfl⟩
      exact u.property
    · intro hx
      let u : VFType (M := M) := ⟨x,hx⟩
      refine ⟨u,?_,rfl⟩
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (show u-0 ∈ H from trivial)
  exact atomic_ball_coset_below_complete_type Q H hH hA i ⟨0,hi.trans hc.symm⟩ hsub

end IntegrationInACVF.Section3ACVF.GammaRadiusAtomicity
