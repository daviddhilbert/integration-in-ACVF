import IntegrationSection6.NativePolynomialLifts
import Section7.BalancedCorrespondence

/-! Balanced correspondence lifting with native definability retained,
including zero coordinates. Adapted from the checked zero-deletion proof
in Special transformations, Section7/BalancedCorrespondence.lean, revision
9cc9760892092dd34cfad4a6dee655843c52f30c (MIT per Lake metadata). -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section7
namespace IntegrationInACVF.Section6
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
local notation "N" => (@CanonicalStructure.normalize M sM)

theorem exists_native_balanced_correspondence_lift {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hsat : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    (n : ℕ) (C : Set (Fin (n + n) → M)) (hC : DefinableOverBase B (fun _ => .rv) C)
    (hbal : ∀ t s, productTuple t s ∈ C → rawWeight t = rawWeight s)
    (hleft : ∀ b : Fin n → M, {a : Fin n → M | productTuple a b ∈ C}.Finite)
    (hright : ∀ a : Fin n → M, {b : Fin n → M | productTuple a b ∈ C}.Finite) :
    ∃ A : Set (Fin (n + n) → M), @Set.Definable M B.real LRV N (Fin (n+n)) A ∧ C ⊆ rawLiftDomain A := by
  classical
  induction n with
  | zero =>
    obtain ⟨A, hA, hgood⟩ := exists_nonzero_native_lift hκ hsat h00 hsmall hB v hv C hC
      (fun _ _ i => i.elim0) hleft hright
    exact ⟨A, hA, hgood⟩
  | succ n ih =>
    let Rnz : Set (Fin ((n + 1) + (n + 1)) → M) := {z | ∀ i, NonzeroRV (z i)}
    let D := C ∩ Rnz
    have hD : DefinableOverBase B (fun _ => .rv) D :=
      hC.inter (real_definableOverBase B _ Rnz (nonzeroRVTuple_definable B.real _))
    obtain ⟨A₀, hA₀, hgood₀⟩ := exists_nonzero_native_lift hκ hsat h00 hsmall hB v hv D hD
      (fun z hz i => (hz.2 i).2)
      (fun b => (hleft b).subset (fun _ hz => hz.1))
      (fun a => (hright a).subset (fun _ hz => hz.1))
    apply exists_native_gamma_glued_lift hκ hsat hsmall C hC
    intro z hz
    by_cases hz0 : ∀ i, z i ≠ iRVZero
    · exact ⟨A₀, hA₀, hgood₀ ⟨hz, fun i => ⟨by
        simpa only [sortEval, iRV] using hC.proper _ hz i, hz0 i⟩⟩⟩
    · let t := z ∘ productLeft (n + 1) (n + 1)
      let s := z ∘ productRight (n + 1) (n + 1)
      have hzip : productTuple t s = z := by
        apply productTuple_ext
        · intro i; exact productTuple_left t s i
        · intro j; exact productTuple_right t s j
      have hts : productTuple t s ∈ C := by rwa [hzip]
      have hw := hbal t s hts
      have hzero : (∃ i, t i = iRVZero) ∨ ∃ j, s j = iRVZero := by
        push Not at hz0
        obtain ⟨l, hl⟩ := hz0
        obtain ⟨k, rfl⟩ := finSumFinEquiv.surjective l
        cases k with
        | inl i => exact Or.inl ⟨i, hl⟩
        | inr j => exact Or.inr ⟨j, hl⟩
      have ht : ∃ i, t i = iRVZero := hzero.elim id (fun h =>
        (rawWeight_le_pred_iff_zero t).mp (hw.trans_le ((rawWeight_le_pred_iff_zero s).mpr h)))
      have hs : ∃ j, s j = iRVZero :=
        (rawWeight_le_pred_iff_zero s).mp (hw.symm.trans_le ((rawWeight_le_pred_iff_zero t).mpr ht))
      obtain ⟨i, hi⟩ := ht
      obtain ⟨j, hj⟩ := hs
      let C' : Set (Fin (n + n) → M) := {w | padZeroPair i j w ∈ C}
      have hC' : DefinableOverBase B (fun _ => .rv) C' :=
        zeroPadded_correspondence_definable B i j C hC
      have hbal' (a b : Fin n → M) (hab : productTuple a b ∈ C') :
          rawWeight a = rawWeight b := by
        change padZeroPair i j (productTuple a b) ∈ C at hab
        rw [padZeroPair_productTuple] at hab
        simpa only [rawWeight_insertZero] using hbal _ _ hab
      have hinsert (k : Fin (n + 1)) :
          Function.Injective (Fin.insertNth (α := fun _ : Fin (n + 1) => M) k iRVZero) := by
        intro a b he
        simpa only [Fin.removeNth_insertNth] using congrArg k.removeNth he
      have hleft' (b : Fin n → M) : {a : Fin n → M | productTuple a b ∈ C'}.Finite := by
        apply Set.Finite.of_injOn (f := Fin.insertNth i iRVZero) ?_ (hinsert i).injOn
          (hleft (Fin.insertNth j iRVZero b))
        intro a ha
        change padZeroPair i j (productTuple a b) ∈ C at ha
        rwa [padZeroPair_productTuple] at ha
      have hright' (a : Fin n → M) : {b : Fin n → M | productTuple a b ∈ C'}.Finite := by
        apply Set.Finite.of_injOn (f := Fin.insertNth j iRVZero) ?_ (hinsert j).injOn
          (hright (Fin.insertNth i iRVZero a))
        intro b hb
        change padZeroPair i j (productTuple a b) ∈ C at hb
        rwa [padZeroPair_productTuple] at hb
      obtain ⟨A, hA, hgood⟩ := ih C' hC' hbal' hleft' hright'
      have hshort : productTuple (t ∘ i.succAbove) (s ∘ j.succAbove) ∈ C' := by
        have he : Fin.insertNth i iRVZero (t ∘ i.succAbove) = t :=
          Fin.insertNth_eq_iff.mpr ⟨hi.symm, rfl⟩
        have hf : Fin.insertNth j iRVZero (s ∘ j.succAbove) = s :=
          Fin.insertNth_eq_iff.mpr ⟨hj.symm, rfl⟩
        change padZeroPair i j _ ∈ C
        rwa [padZeroPair_productTuple, he, hf]
      refine ⟨{x | x ∘ deletePairCoordinates i j ∈ A},
        (by
          letI : LRV.Structure M := N
          exact hA.preimage_comp (deletePairCoordinates i j)), ?_⟩
      rw [← hzip]
      exact rawLiftDomain_deleteZero_pair i j t s hi hj A (hgood hshort)


end IntegrationInACVF.Section6
