import IntegrationSection3ACVF.FullGammaSyntax

/-!
# An original-base definable Gamma point

Adapts the pinned predecessor's GammaControllerDefinability,
GammaFiniteDefinablePoints and GammaDefinableClosure proofs. Real-code
specialization proves existence of an order controller; its intrinsic
minimality recovers definability over the original combined base.
-/

set_option backward.isDefEq.respectTransparency false

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open IntegrationInACVF.Section3
open IntegrationInACVF.Section3ACVF.FullGammaSyntax

namespace IntegrationInACVF.Section3ACVF.FullGammaPoint

variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {B : FullBaseAtomicity.Base (M := M)}

theorem real_specialization {A : Set (Values.Gamma (M := M))} (hA : Scalar B A) :
    ∃ F : Set M, F.Finite ∧ Values.GammaDefinable (B.real ∪ F) A := by
  let U := Values.gammaPullback A
  have hsub : U ⊆ {x | iRV x} := fun _ hx => hx.choose
  have hs : ∃ F : Set M, F.Finite ∧
      @Set.Definable M (B.real ∪ F) LRV (CanonicalStructure.normalize (M := M))
        (Fin 1) {z | z 0 ∈ U} := by
    letI := CanonicalStructure.normalize (M := M)
    exact ImaginaryParameters.OverBase.specialize hA
  obtain ⟨F,hF,hs⟩ := hs
  exact ⟨F,hF,(@definableAt_iff_normalized_raw M sM hM (B.real ∪ F) .rv _).mpr ⟨hs,hsub⟩⟩

theorem tupleControls_definable (A : Set (Values.Gamma (M := M))) (hA : Scalar B A) (n : ℕ) :
    Definable B (fun c : Fin n → Values.Gamma (M := M) => FiniteOrder.TupleControls c A) := by
  have hpat : Definable B (fun z : Fin n ⊕ Fin 2 → Values.Gamma (M := M) =>
      ∀ i, (z (.inr 0) < z (.inl i) ↔ z (.inr 1) < z (.inl i)) ∧
        (z (.inl i) < z (.inr 0) ↔ z (.inl i) < z (.inr 1))) :=
    Definable.forall_finite (fun i =>
      ((lt_definable B (Sum.inr 0) (Sum.inl i)).iff
        (lt_definable B (Sum.inr 1) (Sum.inl i))).and
      ((lt_definable B (Sum.inl i) (Sum.inr 0)).iff
        (lt_definable B (Sum.inl i) (Sum.inr 1))))
  have hm := (unary_at hA (Sum.inr (0 : Fin 2) : Fin n ⊕ Fin 2)).iff
    (unary_at hA (Sum.inr (1 : Fin 2) : Fin n ⊕ Fin 2))
  have h := (hpat.imp hm).forall_block
  exact h.congr (fun c => by
    constructor
    · intro hc x y hp
      exact hc ![x,y] hp
    · intro hc p
      exact hc (p 0) (p 1))

theorem minimal_controller_definable (A : Set (Values.Gamma (M := M))) (hA : Scalar B A)
    (F : Finset (Values.Gamma (M := M))) (hF : FiniteOrder.Controls F A)
    (hmin : ∀ H, FiniteOrder.Controls H A → F.card ≤ H.card) :
    Scalar B (F : Set (Values.Gamma (M := M))) := by
  let ι := Fin 1 ⊕ Fin F.card
  have hc := (tupleControls_definable A hA F.card).reindex (Sum.inr : Fin F.card → ι)
  have hi : Definable B (fun z : ι → Values.Gamma (M := M) =>
      ∃ i : Fin F.card, z (.inr i) = z (.inl 0)) := by
    have h := (Definable.forall_finite (fun i : Fin F.card =>
      (eq_definable B (Sum.inr i : ι) (Sum.inl 0)).not)).not
    exact h.congr (fun z => by simp only [not_forall,not_not])
  have he := (hc.and hi).exists_block
  apply (scalar_definable_iff (F : Set (Values.Gamma (M := M)))).mp
  exact he.congr (fun z => (FiniteOrder.minimal_controller_mem_iff_tuple hF hmin (z 0)).symm)

theorem exists_definable_minimal_controller (h00 : M ⊨ Axioms.ACVF00)
    (A : Set (Values.Gamma (M := M))) (hA : Scalar B A) :
    ∃ F : Finset (Values.Gamma (M := M)), FiniteOrder.Controls F A ∧
      Scalar B (F : Set (Values.Gamma (M := M))) ∧
      ∀ H, FiniteOrder.Controls H A → F.card ≤ H.card := by
  obtain ⟨E,_,hAr⟩ := real_specialization hA
  obtain ⟨F,hF,_,hmin⟩ := exists_definable_minimal_gamma_controller h00 A hAr
  exact ⟨F,hF,minimal_controller_definable A hA F hF hmin,hmin⟩

theorem scalar_sdiff {A C : Set (Values.Gamma (M := M))}
    (hA : Scalar B A) (hC : Scalar B C) : Scalar B (A \ C) :=
  (scalar_definable_iff (A \ C)).mp
    (((scalar_definable_iff A).mpr hA).and ((scalar_definable_iff C).mpr hC).not)

theorem finset_min_definable (F : Finset (Values.Gamma (M := M)))
    (hF : Scalar B (F : Set (Values.Gamma (M := M)))) (hne : F.Nonempty) :
    Scalar B {F.min' hne} := by
  let ι := Fin 1 ⊕ Fin 1
  have hl := (unary_at hF (Sum.inr (0 : Fin 1) : ι)).and
    (lt_definable B (Sum.inr (0 : Fin 1) : ι) (Sum.inl 0))
  have h := ((scalar_definable_iff (F : Set (Values.Gamma (M := M)))).mpr hF).and
    hl.exists_block.not
  apply (scalar_definable_iff {F.min' hne}).mp
  exact h.congr (fun a => by
    change (a 0 ∈ F ∧ ¬ ∃ b : Fin 1 → Values.Gamma (M := M), b 0 ∈ F ∧ b 0 < a 0) ↔
      a 0 = F.min' hne
    constructor
    · rintro ⟨ha,hb⟩
      exact le_antisymm (le_of_not_gt (fun he => hb ⟨![F.min' hne],F.min'_mem hne,he⟩))
        (F.min'_le _ ha)
    · intro he
      refine ⟨he.symm ▸ F.min'_mem hne,?_⟩
      rintro ⟨b,hb,hba⟩
      rw [he] at hba
      exact not_lt_of_ge (F.min'_le _ hb) hba)

theorem finset_element_definable (F : Finset (Values.Gamma (M := M)))
    (hF : Scalar B (F : Set (Values.Gamma (M := M))))
    (c : Values.Gamma (M := M)) (hc : c ∈ F) : Scalar B {c} := by
  revert hF c
  induction F using Finset.strongInductionOn
  rename_i F ih
  intro hF c hc
  have hne : F.Nonempty := ⟨c,hc⟩
  let m := F.min' hne
  have hm : Scalar B {m} := finset_min_definable F hF hne
  by_cases he : c = m
  · exact he.symm ▸ hm
  · have hE : Scalar B ((F.erase m : Finset _) : Set (Values.Gamma (M := M))) := by
      simpa only [Finset.coe_erase] using scalar_sdiff hF hm
    exact ih (F.erase m) (Finset.erase_ssubset (F.min'_mem hne)) hE c
      (Finset.mem_erase.mpr ⟨he,hc⟩)

def Named (B : FullBaseAtomicity.Base (M := M)) : Set (Values.Gamma (M := M)) :=
  {γ | Scalar B {γ}}

theorem named_one : (1 : Values.Gamma (M := M)) ∈ Named B := one_definable B

theorem named_mul {a b : Values.Gamma (M := M)} (ha : a ∈ Named B) (hb : b ∈ Named B) :
    a * b ∈ Named B := by
  let ι := Fin 1 ⊕ Fin 2
  have h := ((unary_at ha (Sum.inr (0 : Fin 2) : ι)).and
    (unary_at hb (Sum.inr (1 : Fin 2) : ι))).and
    (mul_definable B (Sum.inr (0 : Fin 2) : ι) (Sum.inr 1) (Sum.inl 0))
  apply (scalar_definable_iff {a * b}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 2 → Values.Gamma (M := M),
      (t 0 = a ∧ t 1 = b) ∧ t 0 * t 1 = z 0) ↔ z 0 = a * b
    constructor
    · rintro ⟨t,⟨ha,hb⟩,ht⟩
      rw [ha,hb] at ht
      exact ht.symm
    · intro he
      exact ⟨![a,b],⟨rfl,rfl⟩,he.symm⟩)

theorem named_inv {a : Values.Gamma (M := M)} (ha : a ∈ Named B) : a⁻¹ ∈ Named B := by
  let ι := Fin 1 ⊕ Fin 2
  have h := ((unary_at ha (Sum.inr (0 : Fin 2) : ι)).and
    (unary_at (named_one (B := B)) (Sum.inr (1 : Fin 2) : ι))).and
    (mul_definable B (Sum.inr (0 : Fin 2) : ι) (Sum.inl 0) (Sum.inr 1))
  apply (scalar_definable_iff {a⁻¹}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 2 → Values.Gamma (M := M),
      (t 0 = a ∧ t 1 = 1) ∧ t 0 * z 0 = t 1) ↔ z 0 = a⁻¹
    constructor
    · rintro ⟨t,⟨ha,hb⟩,ht⟩
      rw [ha,hb] at ht
      exact mul_left_cancel (ht.trans (mul_inv_cancel a).symm)
    · intro he
      exact ⟨![a,1],⟨rfl,rfl⟩,by change a * z 0 = 1; rw [he,mul_inv_cancel]⟩)

theorem named_square_root {a : Values.Gamma (M := M)} (ha : a ∈ Named B) :
    ∃ r ∈ Named B, r * r = a := by
  obtain ⟨r,hr⟩ := Values.gamma_pow_surjective (M := M) 2 (by decide) a
  have hrr : r * r = a := by simpa only [pow_two] using hr
  refine ⟨r,?_,hrr⟩
  let ι := Fin 1 ⊕ Fin 1
  have h := (unary_at ha (Sum.inr (0 : Fin 1) : ι)).and
    (mul_definable B (Sum.inl (0 : Fin 1) : ι) (Sum.inl 0) (Sum.inr 0))
  apply (scalar_definable_iff {r}).mp
  exact h.exists_block.congr (fun z => by
    change (∃ t : Fin 1 → Values.Gamma (M := M), t 0 = a ∧ z 0 * z 0 = t 0) ↔ z 0 = r
    constructor
    · rintro ⟨t,ht,hz⟩
      exact gamma_square_injective (hz.trans (ht.trans hrr.symm))
    · intro hz
      exact ⟨![a],rfl,by change z 0 * z 0 = a; rw [hz,hrr]⟩)

theorem named_samples (δ : Values.Gamma (M := M)) (hδ : δ ∈ Named B) (hδ1 : 1 < δ) :
    (∀ a ∈ Named B, ∃ b ∈ Named B, b < a) ∧
    (∀ a ∈ Named B, ∃ b ∈ Named B, a < b) ∧
    (∀ a ∈ Named B, ∀ b ∈ Named B, a < b → ∃ c ∈ Named B, a < c ∧ c < b) := by
  refine ⟨?_,?_,?_⟩
  · intro a ha
    refine ⟨a * δ⁻¹,named_mul ha (named_inv hδ),?_⟩
    have hi : δ⁻¹ < 1 := Left.inv_lt_one_iff.mpr hδ1
    simpa only [mul_one] using mul_lt_mul_right hi a
  · intro a ha
    refine ⟨a * δ,named_mul ha hδ,?_⟩
    simpa only [mul_one] using mul_lt_mul_right hδ1 a
  · intro a ha b hb hab
    obtain ⟨r,hr,hrr⟩ := named_square_root (named_mul ha hb)
    refine ⟨r,hr,?_,?_⟩
    · apply lt_of_not_ge
      intro hra
      have hle : r * r ≤ a * a := mul_le_mul' hra hra
      have hlt : a * a < a * b := mul_lt_mul_right hab a
      rw [hrr] at hle
      exact not_le_of_gt hlt hle
    · apply lt_of_not_ge
      intro hbr
      have hle : b * b ≤ r * r := mul_le_mul' hbr hbr
      have hlt : a * b < b * b := mul_lt_mul_left hab b
      rw [hrr] at hle
      exact not_le_of_gt hlt hle

/-- A nonempty definable Gamma set has a point definable over the original
real/Gamma/ball base. The standing nontrivial named value is explicit. -/
theorem gamma_definable_point (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (Values.Gamma (M := M))) (hA : Scalar B A) (hne : A.Nonempty) :
    ∃ γ ∈ A, Scalar B {γ} := by
  obtain ⟨F,hF,hFd,_⟩ := exists_definable_minimal_controller h00 A hA
  have hFD : (F : Set (Values.Gamma (M := M))) ⊆ Named B :=
    fun c hc => finset_element_definable F hFd c hc
  obtain ⟨hbelow,habove,hbetween⟩ := named_samples δ hδ hδ1
  obtain ⟨γ,hγA,hγD⟩ := FiniteOrder.nonempty_inter_of_controls F A (Named B)
    hF hne ⟨1,named_one⟩ hFD hbelow habove hbetween
  exact ⟨γ,hγA,hγD⟩

end IntegrationInACVF.Section3ACVF.FullGammaPoint
