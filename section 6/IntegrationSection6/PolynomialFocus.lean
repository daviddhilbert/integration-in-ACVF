import Section7.CorrespondenceLifting

/-! The local polynomial focus used in Lemma 6.12. A simple residue root
in the active coordinate gives a unique section over every other field
representative, with coefficients in the original generated VF base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open Classical MvPolynomial
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section7

namespace IntegrationInACVF.Section6

section PolynomialSection

variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

private def singleCoordinate {n : ℕ} (j : Fin n) : Fin 1 ↪ Fin n :=
  ⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩

private theorem extend_singleCoordinate {n : ℕ} (j : Fin n)
    (a : Fin n → K) (b : Fin 1 → K) :
    Function.extend (singleCoordinate j) b a = Function.update a j (b 0) := by
  funext i
  by_cases hi : i = j
  · subst i
    rw [Function.update_self]
    change Function.extend (singleCoordinate j) b a ((singleCoordinate j) 0) = b 0
    exact (singleCoordinate j).injective.extend_apply b a (0 : Fin 1)
  · rw [Function.extend_apply' _ _ _ (by rintro ⟨k, hk⟩; exact hi hk.symm)]
    simp [Function.update_of_ne hi]

/-- The Hensel conclusion with all unchanged coordinates retained. -/
theorem polynomialFocus_section [IsAlgClosed K] (v : Valuation K Γ)
    {n : ℕ} (t : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none)
    (j : Fin n) {α : Γ} (P : MvPolynomial (Fin n) K)
    (hP : IsGammaPolynomial v (fun i => RVCalc.vrv v (t i)) α P)
    (hr : IsResidueRoot v t α P)
    (hd : ¬ IsResidueRoot v t (α / RVCalc.vrv v (t j)) (pderiv j P))
    (a : Fin n → K) (ha : a ∈ RVFibre v t) :
    ∃! b : Fin n → K, b ∈ RVFibre v t ∧ P.eval b = 0 ∧
      ∀ i, i ≠ j → b i = a i := by
  let f := singleCoordinate j
  have hJ : ¬ IsResidueRoot v t
      (jacobianValue (fun i => RVCalc.vrv v (t (f i))) (fun _ : Fin 1 => α))
      (partialJacobianPolynomial f (fun _ : Fin 1 => P)) := by
    simpa [jacobianValue, partialJacobianPolynomial, Matrix.det_fin_one, f,
      singleCoordinate] using hd
  have hs := simpleResidueRoot_specializeCoordinates v ht (fun _ : Fin 1 => hP)
    (fun _ => hr) f hJ a ha
  obtain ⟨b, hb, huniq⟩ := generalized_hensel v hs
  let c := Function.update a j (b 0)
  have hext : Function.extend f b a = c := extend_singleCoordinate j a b
  have hcRV : c ∈ RVFibre v t := by
    intro i
    by_cases hi : i = j
    · subst i; simpa [c, f, singleCoordinate] using hb.1 0
    · simpa [c, hi] using ha i
  have hcP : P.eval c = 0 := by
    have h := hb.2 0
    rw [specializeCoordinates_eval, hext] at h
    exact h
  refine ⟨c, ⟨hcRV, hcP, fun i hi => Function.update_of_ne hi _ _⟩, ?_⟩
  intro d hd'
  have hed : Function.extend f (fun _ : Fin 1 => d j) a = d := by
    rw [extend_singleCoordinate]
    funext i
    by_cases hi : i = j
    · subst i; simp
    · exact (Function.update_of_ne hi _ _).trans (hd'.2.2 i hi).symm
  have hdroot : (fun _ : Fin 1 => d j) ∈ RVFibre v (t ∘ f) ∧
      ∀ i : Fin 1, (specializeCoordinates f a P).eval (fun _ => d j) = 0 := by
    constructor
    · intro i; exact hd'.1 j
    · intro i; rw [specializeCoordinates_eval, hed]; exact hd'.2.1
  have hdb := congrFun (huniq _ hdroot) (0 : Fin 1)
  funext i
  by_cases hi : i = j
  · subst i; simpa [c] using hdb
  · exact (hd'.2.2 i hi).trans (Function.update_of_ne hi _ _).symm

end PolynomialSection

variable {M Γ : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
  [LinearOrderedCommGroupWithZero Γ]

/-- The polynomial equation and its unique fibre section are consequences
of algebraicity, not extra focus-existence hypotheses. -/
theorem exists_originalPolynomial_focus {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00)
    (B : Base (M := M)) (hsmall : Cardinal.mk B.real < κ) (hB : VFGammaGeneratedBase B)
    (v : Valuation (VFType (M := M)) Γ)
    (hv : ∀ x y : VFType (M := M), VFValued.predV x y ↔ v x ≤ v y)
    {r n : ℕ} (f : Fin r ↪ Fin n) (j : Fin n) (hj : j ∉ Set.range f)
    (t : Fin n → RVCalc.RV v) (ht : ∀ i, t i ≠ none)
    (halg : AlgebraicAtBase
      ⟨B.real ∪ Set.range (fun i : Fin r => (CanonicalRV.equiv (M := M) v hv (t (f i))).val), B.gamma⟩
      .rv (CanonicalRV.equiv (M := M) v hv (t j)).val) :
    ∃ P : MvPolynomial (Fin n) (vfDefinableClosureFieldBase B),
      ∀ a ∈ RVFibre v t, ∃! b : Fin n → VFType (M := M),
        b ∈ RVFibre v t ∧ (P.map (vfDefinableClosureFieldBase B).subtype).eval b = 0 ∧
          ∀ i, i ≠ j → b i = a i := by
  obtain ⟨α, P, hP, hr, hd, _⟩ := exists_originalPolynomial_for_coordinate
    hκ hs h00 B hsmall hB v hv f j hj t ht halg
  letI : IsAlgClosed (VFType (M := M)) := VFAlgClosed.isAlgClosed_vfType
  exact ⟨P, polynomialFocus_section v t ht j _ hP hr hd⟩

end IntegrationInACVF.Section6
