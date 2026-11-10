import SpecialTransformations
import IntegrationSection3.Library

/-!
# Actual ACVF inputs for the parametric atomicity argument

Uses the unchanged released language and the predecessor's proved
C-minimality. The conversion to valuation balls follows
`GammaThresholdGeometry.encodedBall_good` at the pinned predecessor revision,
retaining the stronger single-ball property needed here.

This module is separate from the language-generic core so the latter can be
checked without rebuilding the full predecessor. It is checked by the root
build and the ACVF headline audit in GitHub Actions.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open IntegrationInACVF.Section3

namespace IntegrationInACVF.Section3ACVF

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- The encoded ball is one valuation ball, not just a Boolean combination. -/
theorem encodedBall_isKBall {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (B : Set M) (hB : IsBall B) :
    ValOneEC.IsKBall (RingHom.id (VFType (M := M))) v {x | x.val ∈ B} := by
  rcases hB with hB | ⟨a,t,ha,ht,ht0,hB⟩ | (⟨a,t,ha,ht,ht0,hB⟩ | ⟨a,ha,hB⟩)
  · have he : {x : VFType (M := M) | x.val ∈ B} = Set.univ := by
      ext x
      rw [hB]
      exact iff_true_intro x.property
    rw [he]
    exact .univ
  · let a' : VFType (M := M) := ⟨a,ha⟩
    obtain ⟨b,hb⟩ := CanonicalRV.encodedRv_surjective (⟨t,ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have he : {x : VFType (M := M) | x.val ∈ B} = ValOneEC.closedBall v a' (v b) := by
      ext x
      change x.val ∈ B ↔ v (x-a') ≤ v b
      rw [hB]
      change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a)))) ↔ _
      rw [and_iff_right x.property]
      have hd : (x-a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
      have hh := hv (x-a') b
      change iLe (iRv b.val) (iRv (x-a').val) ↔ _ at hh
      rw [hb',hd] at hh
      exact hh
    rw [he]
    exact .closed a' b
  · let a' : VFType (M := M) := ⟨a,ha⟩
    obtain ⟨b,hb⟩ := CanonicalRV.encodedRv_surjective (⟨t,ht⟩ : CanonicalRV.RVSort M)
    have hb' : iRv b.val = t := congrArg Subtype.val hb
    have he : {x : VFType (M := M) | x.val ∈ B} = ValOneEC.openBall v a' (v b) := by
      ext x
      change x.val ∈ B ↔ v (x-a') < v b
      rw [hB]
      change (iVF x.val ∧ iLe t (iRv (iVFAdd x.val (iVFNeg a))) ∧
        ¬ iLe (iRv (iVFAdd x.val (iVFNeg a))) t) ↔ _
      rw [and_iff_right x.property]
      have hd : (x-a').val = iVFAdd x.val (iVFNeg a) := by rw [sub_eq_add_neg]; rfl
      have hle := hv (x-a') b
      have hge := hv b (x-a')
      change iLe (iRv b.val) (iRv (x-a').val) ↔ _ at hle
      change iLe (iRv (x-a').val) (iRv b.val) ↔ _ at hge
      rw [hb',hd] at hle hge
      rw [hle,hge,lt_iff_le_not_ge]
    rw [he]
    exact .openball a' b
  · let a' : VFType (M := M) := ⟨a,ha⟩
    have he : {x : VFType (M := M) | x.val ∈ B} = {a'} := by
      ext x
      rw [hB]
      change (iVF x.val ∧ x.val = a) ↔ x = a'
      rw [and_iff_right x.property]
      exact ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
    rw [he, ← ValOneEC.closedBall_zero_radius v a']
    simpa only [map_zero] using
      (ValOneEC.IsKBall.closed (f := RingHom.id _) (w := v) a' 0)

/-- Open/closed encoded balls, singletons and VF itself form a laminar family. -/
theorem encodedBalls_laminar : IsLaminar {B : Set M | IsBall B} := by
  intro B hB C hC
  by_cases hdis : Disjoint B C
  · exact Or.inr (Or.inr hdis)
  obtain ⟨x,hxB,hxC⟩ := Set.not_disjoint_iff.mp hdis
  obtain ⟨Γ,hΓ,v,hv⟩ := VFValued.exists_valuation_predV (M := M)
  letI := hΓ
  have hxVF := isBall_subset_vf B hB hxB
  have hmeet : ({z : VFType (M := M) | z.val ∈ B} ∩
      {z : VFType (M := M) | z.val ∈ C}).Nonempty :=
    ⟨⟨x,hxVF⟩,hxB,hxC⟩
  rcases ValOneEC.isKBall_subset_or_subset
      (encodedBall_isKBall v hv B hB) (encodedBall_isKBall v hv C hC) hmeet with h | h
  · left
    intro y hy
    exact h (a := (⟨y,isBall_subset_vf B hB hy⟩ : VFType (M := M))) hy
  · right; left
    intro y hy
    exact h (a := (⟨y,isBall_subset_vf C hC hy⟩ : VFType (M := M))) hy

theorem support_of_isBoolComb {balls : Set (Set M)} {S : Set M}
    (h : IsBoolComb balls S) : HasFiniteBallSupport balls S := by
  induction h with
  | basic hb => exact .basic hb
  | univ => exact .univ _
  | compl _ ih => exact ih.compl
  | union _ _ ih ih' => exact ih.union ih'

/-- C-minimality is supplied by the predecessor's theorem, with raw
definability interpreted in its canonical normalization. -/
theorem normalized_cMinimalOn (Q : Set M) :
    @CMinimalOn M LRV (CanonicalStructure.normalize (M := M)) Q
      {x | iVF x} {B : Set M | IsBall B} := by
  intro S hS hsub
  have hsorted : DefinableAt Q .vf S :=
    (definableAt_iff_normalized_raw Q .vf S).mpr ⟨hS,hsub⟩
  obtain ⟨p,φ,hφ,hset⟩ := hsorted.1
  have hb := theorem_2_8_c_minimal (M := M)
    (Fin p.length) p.sorts φ hφ p.values p.sorted
  have he : {x : M | iVF x ∧ φ.Realize p.values ![x]} = S := by
    ext x
    have hx := (Set.ext_iff.mp hset ![x]).symm
    simpa only [Set.mem_ofPred_eq, Fin.forall_fin_one, sortEval] using hx
  rw [he] at hb
  exact support_of_isBoolComb hb

/-- Real-index case of the parametric ball theorem in the released ACVF
language. Imaginary ball-index parameters are not represented by this
statement; the language-generic theorem remains the interface for that case. -/
theorem real_parametric_ball_atomic (Q T : Set M) (C : Set (M × M))
    (hT : @Set.Definable₁ M Q LRV (CanonicalStructure.normalize (M := M)) T)
    (hC : @Set.Definable₂ M Q LRV (CanonicalStructure.normalize (M := M)) C)
    (hballs : ∀ t ∈ T, IsBall (DefinableFamilies.fibre C t))
    (hdis : T.Pairwise fun t u => Disjoint (DefinableFamilies.fibre C t)
      (DefinableFamilies.fibre C u))
    {t : M} (ht : t ∈ T)
    (hna : ¬ @DefinableFamilies.IsAlgebraicPoint M LRV
      (CanonicalStructure.normalize (M := M)) Q t) :
    @IsAtomic LRV M (CanonicalStructure.normalize (M := M)) (Fin 1) (insert t Q)
      {z | z 0 ∈ DefinableFamilies.fibre C t} := by
  have hlam := encodedBalls_laminar (M := M)
  have hcm := normalized_cMinimalOn (M := M) Q
  have hsub := isBall_subset_vf (M := M)
  letI := CanonicalStructure.normalize (M := M)
  exact parametric_ball_atomic hlam hcm hsub hT hC hballs hdis ht hna

end IntegrationInACVF.Section3ACVF
