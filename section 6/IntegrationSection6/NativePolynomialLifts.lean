import IntegrationSection6.NativeGammaLiftGluing
import Section7.CorrespondenceLifting

/-! Native definability of the polynomial local lifts in the pinned
CorrespondenceLifting proof. The mathematical local polynomial systems
are reused; their sorted definability is retained instead of discarded.
Adapted from Special transformations, Section7/CorrespondenceLifting.lean,
pinned revision9cc9760892092dd34cfad4a6dee655843c52f30c (MIT as declared in its Lake metadata). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {n : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem exists_local_nonzero_native_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (C : Set (Fin (n+n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∀ z ∈ C, ∃ A : Set (Fin (n+n) → M), @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ z ∈ rawLiftDomain A := by
  let E := vfDefinableClosureFieldBase B
  intro z hz
  let t : Fin n → _root_.RVCalc.RV v := fun i =>
    (CanonicalRV.equiv v hv).symm ⟨z (productLeft n n i), by
      simpa only [sortEval, iRV] using hC.proper z hz (productLeft n n i)⟩
  let s : Fin n → _root_.RVCalc.RV v := fun i =>
    (CanonicalRV.equiv v hv).symm ⟨z (productRight n n i), by
      simpa only [sortEval, iRV] using hC.proper z hz (productRight n n i)⟩
  have ht_raw (i : Fin n) : rawRV v hv t i = z (productLeft n n i) := by
    simp [rawRV, t]
  have hs_raw (i : Fin n) : rawRV v hv s i = z (productRight n n i) := by
    simp [rawRV, s]
  have hz_eq : productTuple (rawRV v hv t) (rawRV v hv s) = z := by
    apply productTuple_ext
    · intro i; simpa only [productTuple_left] using ht_raw i
    · intro i; simpa only [productTuple_right] using hs_raw i
  have hnone : (CanonicalRV.equiv v hv (none : _root_.RVCalc.RV v)).val = iRVZero := by
    rw [← _root_.RVCalc.rv_zero, CanonicalRV.equiv_rv]
    exact RVCalc.rv_zero_eq hM
  have ht (i : Fin n) : t i ≠ none := by
    intro he
    have h := ht_raw i
    rw [rawRV, he, hnone] at h
    exact h0 z hz _ h.symm
  have hs (i : Fin n) : s i ≠ none := by
    intro he
    have h := hs_raw i
    rw [rawRV, he, hnone] at h
    exact h0 z hz _ h.symm
  obtain ⟨H, hH⟩ := exists_correspondence_local_polynomials hκ hsat h00 B hsmall hB
    v hv C hC t s ht hs (by
      change productTuple (rawRV v hv t) (rawRV v hv s) ∈ C
      rwa [hz_eq]) (hright _) (hleft _)
  let A := {x | ∀ i, x ∈ PolynomialZero.zeroSet E (H i)}
  have hA (i : Fin n) : @Set.Definable M B.real LRV N (Fin (n+n)) (PolynomialZero.zeroSet E (H i)) :=
    ((definableOver_iff_normalized_raw B.real (fun _ => .vf) (PolynomialZero.zeroSet E (H i))).mp
      (PolynomialZero.zeroSet_named_definable B.real E
        (fun c => (mem_generatedBase_vfField B hB c.val).mp c.property) (H i))).1
  have hAd : @Set.Definable M B.real LRV N (Fin (n+n)) A := by
    letI : LRV.Structure M := N
    convert Set.definable_iInter_of_finite hA using 1
    ext x
    simp [A]
  have hmem (p : (Fin n → VFType (M := M)) × (Fin n → VFType (M := M))) :
      productTuple (rawVF p.1) (rawVF p.2) ∈ A ↔
        ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0 := by
    have he : productTuple (rawVF p.1) (rawVF p.2) = rawVF (productTuple p.1 p.2) := by
      apply productTuple_ext
      · intro i; simp [rawVF]
      · intro i; simp [rawVF]
    rw [he]
    apply forall_congr'
    intro i
    rw [MvPolynomial.eval_map]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨fun j => (productTuple p.1 p.2 j).property, h⟩⟩
  refine ⟨A, hAd, ?_⟩
  rw [← hz_eq]
  apply (rawLiftDomain_mem_iff v hv A t s).mpr
  have he : {p : (Fin n → VFType (M := M)) × (Fin n → VFType (M := M)) |
      productTuple (rawVF p.1) (rawVF p.2) ∈ A} =
      {p | ∀ i, ((H i).map E.subtype).eval (productTuple p.1 p.2) = 0} := Set.ext hmem
  rw [he]
  exact hH

theorem exists_nonzero_native_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (C : Set (Fin (n+n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (h0 : ∀ z ∈ C, ∀ i, z i ≠ iRVZero)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∃ A : Set (Fin (n+n) → M), @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ C ⊆ rawLiftDomain A :=
  exists_native_gamma_glued_lift hκ hsat hsmall C hC
    (exists_local_nonzero_native_lift hκ hsat h00 hsmall hB v hv C hC h0 hleft hright)

end IntegrationInACVF.Section6
