import IntegrationSection3ACVF.BallCosetAtomicity

/-!
# Balls at radii named over the real base

The radius is an RV element in the original parameter set. A VF lift is
chosen only inside the proof that its zero-centred ball is an additive
subgroup. Neither the centre nor that lift is added to the base.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3.ImaginaryFamilies
open IntegrationInACVF.Section3ACVF.BallCosetAtomicity

namespace IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- `strict = true` denotes a proper open ball. -/
def radiusTail (t : M) (strict : Bool) : Set M :=
  {u | iRV u ∧ iLe t u ∧ (strict = true → ¬ iLe u t)}

def radiusBall (a : VFType (M := M)) (t : M) (strict : Bool) : Set M :=
  {x | iVF x ∧ iLe t (iRv (iVFAdd x (iVFNeg a.val))) ∧
    (strict = true → ¬ iLe (iRv (iVFAdd x (iVFNeg a.val))) t)}

/-- The full RV tail is definable over the original base, without a VF lift. -/
theorem radiusTail_definable (Q : Set M) (t : M) (ht : iRV t) (hQt : t ∈ Q)
    (strict : Bool) : DefinableAt Q .rv (radiusTail t strict) := by
  let T := radiusTail t strict
  have hs := ((@definableAt_iff_normalized_raw M sM hM Q .rv _).mp
    (@definableAt_sort M sM Q .rv)).1
  have hnorm (u : M) (hu : iRV u) := rv_le_normalize t u ht hu
  have hnorm' (u : M) (hu : iRV u) := rv_le_normalize u t hu ht
  apply (@definableAt_iff_normalized_raw M sM hM Q .rv T).mpr
  refine ⟨?_, fun _ hu => hu.1⟩
  let N := CanonicalStructure.normalize (M := M)
  letI := N
  have hc : Q.DefinableFun LRV (fun _ : Fin 1 → M => t) :=
    LRV.definableFun_const (Fin 1) hQt
  have hx : Q.DefinableFun LRV (fun z : Fin 1 → M => z 0) := Set.DefinableFun.proj LRV
  have hl := (GammaParameters.raw_le_definable (M := M) Q).preimage_map
    (show Q.DefinableMap LRV (fun z : Fin 1 → M => ![t,z 0]) from by
      intro i; fin_cases i; exact hc; exact hx)
  have hr := (GammaParameters.raw_le_definable (M := M) Q).preimage_map
    (show Q.DefinableMap LRV (fun z : Fin 1 → M => ![z 0,t]) from by
      intro i; fin_cases i; exact hx; exact hc)
  change Q.Definable LRV {z : Fin 1 → M | z 0 ∈ T}
  cases strict with
  | false =>
    convert hs.inter hl using 1
    ext z
    change ( @iRV M sM (z 0) ∧ @iLe M sM t (z 0) ∧
      (false = true → ¬ @iLe M sM (z 0) t)) ↔
      (@iRV M sM (z 0) ∧ @iLe M N t (z 0))
    simp only [Bool.false_eq_true, false_implies, and_true]
    exact and_congr_right (fun hu => (hnorm _ hu).symm)
  | true =>
    convert hs.inter (hl.inter hr.compl) using 1
    ext z
    change (@iRV M sM (z 0) ∧ @iLe M sM t (z 0) ∧
      (true = true → ¬ @iLe M sM (z 0) t)) ↔
      (@iRV M sM (z 0) ∧ @iLe M N t (z 0) ∧ ¬ @iLe M N (z 0) t)
    simp only [true_implies]
    exact and_congr_right (fun hu =>
      and_congr (hnorm _ hu).symm (not_congr (hnorm' _ hu).symm))

/-- Every nonzero RV radius gives an actual definable additive subgroup;
all its translates are exactly the encoded balls at that radius. -/
theorem radius_subgroup (Q : Set M) (t : M) (ht : iRV t) (ht0 : t ≠ iRVZero)
    (strict : Bool) (hT : DefinableAt Q .rv (radiusTail t strict)) :
    ∃ H : AddSubgroup (VFType (M := M)),
      DefinableAt Q .vf (Subtype.val '' (H : Set (VFType (M := M)))) ∧
      ∀ a : VFType (M := M), cosetBody H a = radiusBall a t strict := by
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  obtain ⟨r,hr⟩ := CanonicalRV.encodedRv_surjective (⟨t,ht⟩ : CanonicalRV.RVSort M)
  have hrt : iRv r.val = t := congrArg Subtype.val hr
  have hr0 : r ≠ 0 := fun hz =>
    ht0 (hrt.symm.trans ((CanonicalRV.encodedRv_zero_iff r).mpr hz))
  have hvr : v r ≠ 0 := (map_ne_zero v).mpr hr0
  let H : AddSubgroup (VFType (M := M)) :=
    if strict then v.ltAddSubgroup (Units.mk0 (v r) hvr) else v.leAddSubgroup (v r)
  have hmem (x : VFType (M := M)) :
      x ∈ H ↔ iLe t (iRv x.val) ∧ (strict = true → ¬ iLe (iRv x.val) t) := by
    have hl := hv x r
    have hr := hv r x
    change iLe (iRv r.val) (iRv x.val) ↔ v x ≤ v r at hl
    change iLe (iRv x.val) (iRv r.val) ↔ v r ≤ v x at hr
    rw [hrt] at hl hr
    cases strict with
    | false => simpa only [H, Bool.false_eq_true, ↓reduceIte, false_implies, and_true,
        Valuation.mem_leAddSubgroup_iff] using hl.symm
    | true =>
      simp only [H, ↓reduceIte, true_implies, Valuation.mem_ltAddSubgroup_iff,
        Units.val_mk0, hl, hr, lt_iff_le_not_ge]
  have hzero : Subtype.val '' (H : Set (VFType (M := M))) =
      {x | iVF x ∧ iRv x ∈ radiusTail t strict} := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property,rv_mem hM u.property,hmem u |>.mp hu⟩
    · rintro ⟨hx,hu⟩
      exact ⟨⟨x,hx⟩,(hmem ⟨x,hx⟩).mpr hu.2,rfl⟩
  refine ⟨H,hzero.symm ▸ hT.rv_preimage,?_⟩
  intro a
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩
    let u' : VFType (M := M) := u
    have hd : (u'-a).val = iVFAdd u.val (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
    have hq : u'-a ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hu
    have hh := (hmem (u'-a)).mp hq
    rw [hd] at hh
    exact ⟨u.property,hh⟩
  · intro hx
    let u : VFType (M := M) := ⟨x,hx.1⟩
    have hd : (u-a).val = iVFAdd x (iVFNeg a.val) := by rw [sub_eq_add_neg]; rfl
    have hq : u-a ∈ H := (hmem (u-a)).mpr (by rw [hd]; exact hx.2)
    exact ⟨u,QuotientAddGroup.eq_iff_sub_mem.mpr hq,rfl⟩

/-- Real-base case of Lemma 3.4, for ordinary radii represented in the base.
The ambient complete type need not be a definable set. -/
theorem lemma_3_4_named_radius (Q : Set M) (t : M) (ht : iRV t)
    (ht0 : t ≠ iRVZero) (hQt : t ∈ Q) (strict : Bool)
    {A : Set M}
    (hA : @GeneratesCompleteType LRV M (CanonicalStructure.normalize (M := M)) (Fin 1) Q
      {z | z 0 ∈ A})
    (i : BallImaginaries.Ball M) (a : VFType (M := M))
    (hi : BallImaginaries.underlying i = radiusBall a t strict)
    (hsub : BallImaginaries.underlying i ⊆ A) :
    @Presentation.AtomicWith LRV M (CanonicalStructure.normalize (M := M))
      (BallImaginaries.Ball M) (Fin 4) BallPresentation.presentation Q i
      (BallImaginaries.underlying i) := by
  obtain ⟨H,hH,he⟩ := radius_subgroup Q t ht ht0 strict
    (radiusTail_definable Q t ht hQt strict)
  exact atomic_ball_coset_below_complete_type Q H hH hA i
    ⟨a,hi.trans (he a).symm⟩ hsub

end IntegrationInACVF.Section3ACVF.NamedRadiusAtomicity
